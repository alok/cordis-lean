import Cordis.Codec
import Cordis.DurableSettlement

/-!
# JSON-AST durable frame validation

`DurableSettlement` starts from a typed `Log` and a supplied `CrashPrefix`.  This
module adds the persistence-facing AST boundary immediately before that typed
layer: a raw frame contains only natural-number codes and transcript lists, and
an `EntryCodec` explains how an entry code is recovered.  `frameCodec` proves
the in-memory JSON round trip; `scanPrefix` then checks every decoded frame
against the indexed `Log` transition.

The scanner is deliberately strict.  It rejects malformed JSON, a torn JSON
record (for example `null` in the frame array), unknown entry codes, sequence
gaps, wrong previous digests, wrong successor codes, and wrong transcript
digests.  A successful result is a dependent `Log`, not an untyped list.  The
scanner does not parse bytes, fsync a file, or infer an arbitrary crash cut;
those remain outside this AST-level boundary, while `CrashPrefix` supplies the
typed cut when a caller has established one.
-/

namespace Cordis.DurableCodec

open Cordis
open Cordis.DurableSettlement

universe u v

set_option autoImplicit false

/-! ## Raw frames and their JSON codec -/

/-- The serializable fields of a durable frame, with the entry represented by its code. -/
structure RawFrame where
  sequence : Nat
  previous : Digest
  entryCode : Nat
  afterCode : Nat
  digest : Digest
  deriving DecidableEq, Repr

namespace RawFrame

variable {State : Type u} {Entry : Type v}

/-- Erase a typed frame to its numeric wire representation. -/
def ofFrame (spec : Spec State Entry) (frame : Frame Entry) : RawFrame where
  sequence := frame.sequence
  previous := frame.previous
  entryCode := spec.entryCode frame.entry
  afterCode := frame.afterCode
  digest := frame.digest

abbrev Tuple := Nat × (Digest × (Nat × (Nat × Digest)))

def toTuple (frame : RawFrame) : Tuple :=
  (frame.sequence, (frame.previous, (frame.entryCode, (frame.afterCode, frame.digest))))

def ofTuple (tuple : Tuple) : RawFrame where
  sequence := tuple.1
  previous := tuple.2.1
  entryCode := tuple.2.2.1
  afterCode := tuple.2.2.2.1
  digest := tuple.2.2.2.2

theorem ofTuple_toTuple (frame : RawFrame) : ofTuple frame.toTuple = frame := by
  cases frame
  rfl

theorem toTuple_ofTuple (tuple : Tuple) : (ofTuple tuple).toTuple = tuple := by
  rcases tuple with ⟨sequence, previous, entryCode, afterCode, digest⟩
  rfl

end RawFrame

private def rawFrameTupleCodec : Codec RawFrame.Tuple :=
  Codec.prod Codec.nat
    (Codec.prod (Codec.list Codec.nat)
      (Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.list Codec.nat))))

/-- A raw frame is a five-field JSON array via the nested product codec. -/
def frameCodec : Codec RawFrame where
  schema := rawFrameTupleCodec.schema
  encode := fun frame => rawFrameTupleCodec.encode frame.toTuple
  decode := fun json => do
    let tuple ← rawFrameTupleCodec.decode json
    return RawFrame.ofTuple tuple
  roundtrip := by
    intro frame
    rw [rawFrameTupleCodec.decode_encode]
    exact congrArg Except.ok (RawFrame.ofTuple_toTuple frame)

theorem frameCodec_roundtrip (frame : RawFrame) :
    frameCodec.decode (frameCodec.encode frame) = .ok frame := by
  exact frameCodec.decode_encode frame

/-! ## Entry decoding and frame validation -/

/-- The entry-code obligations needed to turn a raw frame back into a typed entry. -/
structure EntryCodec (Entry : Type v) where
  encode : Entry → Nat
  decode : Nat → Option Entry
  decode_encode : ∀ code entry, decode code = some entry → code = encode entry
  roundtrip : ∀ entry, decode (encode entry) = some entry

/-!
`entryCode` is a field of the supplied settlement specification.  Keeping the
decoder separate makes the boundary honest: the scanner can reject an unknown
code instead of inventing an `Entry` value.
-/
structure WireSpec (State : Type u) (Entry : Type v) where
  spec : Spec State Entry
  entries : EntryCodec Entry
  entryCode_eq : ∀ entry, entries.encode entry = spec.entryCode entry

inductive ScanError where
  | sequenceMismatch (expected actual : Nat)
  | previousMismatch (expected actual : Digest)
  | unknownEntry (code : Nat)
  | afterCodeMismatch (expected actual : Nat)
  | digestMismatch (expected actual : Digest)
deriving DecidableEq, Repr

/-- A raw frame together with the exact typed frame it was checked against. -/
structure FrameCheck
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (before : State)
    (nextSequence : Nat) (digest : Digest) (raw : RawFrame) where
  entry : Entry
  raw_eq : raw = RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec digest nextSequence entry before)

/-- Validate one raw frame against the current typed prefix. -/
def checkFrame
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (before : State)
    (nextSequence : Nat) (digest : Digest) (raw : RawFrame) :
    Except ScanError (FrameCheck wire before nextSequence digest raw) := by
  by_cases hSequence : raw.sequence = nextSequence
  · by_cases hPrevious : raw.previous = digest
    · match hEntry : wire.entries.decode raw.entryCode with
      | none => exact .error (.unknownEntry raw.entryCode)
      | some entry =>
          let expectedAfter := wire.spec.stateCode (wire.spec.after entry before)
          by_cases hAfter : raw.afterCode = expectedAfter
          · let expectedDigest :=
              wire.spec.frameDigest digest nextSequence entry expectedAfter
            by_cases hDigest : raw.digest = expectedDigest
            · have hCode : raw.entryCode = wire.spec.entryCode entry := by
                exact (wire.entries.decode_encode raw.entryCode entry hEntry).trans
                  (wire.entryCode_eq entry)
              exact .ok {
                entry
                raw_eq := by
                  cases raw
                  simp_all [RawFrame.ofFrame, Frame.expected]
                  constructor <;> rfl
              }
            · exact .error (.digestMismatch expectedDigest raw.digest)
          · exact .error (.afterCodeMismatch expectedAfter raw.afterCode)
    · exact .error (.previousMismatch digest raw.previous)
  · exact .error (.sequenceMismatch nextSequence raw.sequence)

/-! ## Dependent prefix scanning -/

/-- A successful scan carries an intrinsically indexed settlement log. -/
structure ScannedLog
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State) where
  current : State
  nextSequence : Nat
  digest : Digest
  log : Log wire.spec initial current nextSequence digest

private def scanFramesAux
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State)
    {before : State} {nextSequence : Nat} {digest : Digest}
    (log : Log wire.spec initial before nextSequence digest) :
    List RawFrame → Except ScanError (ScannedLog wire initial)
  | [] => .ok {
      current := before
      nextSequence
      digest
      log
    }
  | raw :: rest =>
      match checkFrame wire before nextSequence digest raw with
      | .error error => .error error
      | .ok checked =>
          scanFramesAux wire initial (Log.append log checked.entry) rest

/-- Strictly scan a decoded raw frame prefix into a proof-carrying `Log`. -/
def scanPrefix
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State) (raw : List RawFrame) :
    Except ScanError (ScannedLog wire initial) :=
  scanFramesAux wire initial .empty raw

private theorem scanFramesAux_frames_exact
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State)
    {before : State} {nextSequence : Nat} {digest : Digest}
    (log : Log wire.spec initial before nextSequence digest)
    (raw : List RawFrame) :
    match scanFramesAux wire initial log raw with
    | .error _ => True
    | .ok scanned =>
        (scanned.log.frames wire.spec initial).map (RawFrame.ofFrame wire.spec) =
          (log.frames wire.spec initial).map (RawFrame.ofFrame wire.spec) ++ raw := by
  induction raw generalizing before nextSequence digest with
  | nil => simp [scanFramesAux]
  | cons head tail inductionHypothesis =>
      cases checked : checkFrame wire before nextSequence digest head with
      | error error => simp [scanFramesAux, checked]
      | ok checkedValue =>
          simp only [scanFramesAux, checked]
          cases tailResult : scanFramesAux wire initial
              (Log.append log checkedValue.entry) tail with
          | error error => simp
          | ok scanned =>
              change (scanned.log.frames wire.spec initial).map
                    (RawFrame.ofFrame wire.spec) =
                  (log.frames wire.spec initial).map (RawFrame.ofFrame wire.spec) ++
                    head :: tail
              have tailExact := inductionHypothesis
                (before := wire.spec.after checkedValue.entry before)
                (nextSequence := nextSequence + 1)
                (digest := wire.spec.frameDigest digest nextSequence checkedValue.entry
                  (wire.spec.stateCode (wire.spec.after checkedValue.entry before)))
                (log := Log.append log checkedValue.entry)
              have tailExact' :
                  (scanned.log.frames wire.spec initial).map
                      (RawFrame.ofFrame wire.spec) =
                    ((Log.append log checkedValue.entry).frames wire.spec initial).map
                        (RawFrame.ofFrame wire.spec) ++ tail := by
                simpa [tailResult] using tailExact
              rw [tailExact']
              simp [Log.frames_tail_is_expected, List.map_append, checkedValue.raw_eq]

theorem scanPrefix_frames_exact
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State) (raw : List RawFrame) :
    match scanPrefix wire initial raw with
    | .error _ => True
    | .ok scanned =>
        (scanned.log.frames wire.spec initial).map (RawFrame.ofFrame wire.spec) = raw := by
  cases h : scanPrefix wire initial raw with
  | error error => trivial
  | ok scanned =>
      have exact := scanFramesAux_frames_exact wire initial
        (log := (Log.empty : Log wire.spec initial initial 0 wire.spec.genesisDigest)) raw
      have haux : scanFramesAux wire initial
          (Log.empty : Log wire.spec initial initial 0 wire.spec.genesisDigest) raw =
          .ok scanned := by
        simpa [scanPrefix] using h
      rw [haux] at exact
      simpa [Log.frames] using exact

/-- Decode a JSON array of raw frames and then run the dependent prefix scanner. -/
def scanJsonPrefix
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State) (json : Lean.Json) :
    Except (DecodeError ⊕ ScanError) (ScannedLog wire initial) :=
  match (Codec.list frameCodec).decode json with
  | .error error => .error (.inl error)
  | .ok raw =>
      match scanPrefix wire initial raw with
      | .error error => .error (.inr error)
      | .ok scanned => .ok scanned

/-! ## Executable examples and exact rejection witnesses -/

namespace Example

def wire : WireSpec Nat Nat where
  spec := DurableSettlement.Example.spec
  entries := {
    encode := id
    decode := fun code => some code
    decode_encode := by
      intro code entry equality
      cases equality
      rfl
    roundtrip := by
      intro entry
      rfl
  }
  entryCode_eq := by intro entry; rfl

def firstRaw : RawFrame :=
  RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec wire.spec.genesisDigest 0 3
      (DurableSettlement.Example.initial))

def secondRaw : RawFrame :=
  RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec
      (DurableSettlement.Example.spec.frameDigest
        DurableSettlement.Example.spec.genesisDigest 0 3 13)
      1 8 13)

def firstJson : Lean.Json := frameCodec.encode firstRaw

def secondJson : Lean.Json := frameCodec.encode secondRaw

def validJson : Lean.Json := (Codec.list frameCodec).encode [firstRaw, secondRaw]

def tornJson : Lean.Json := .arr #[firstJson, .null]

def noncontiguousRaw : RawFrame := { firstRaw with sequence := 4 }

theorem firstRaw_exact : firstRaw = RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec wire.spec.genesisDigest 0 3
      DurableSettlement.Example.initial) := by
  rfl

theorem scan_valid_exact :
    match scanJsonPrefix wire DurableSettlement.Example.initial validJson with
    | .error _ => False
    | .ok scanned =>
        scanned.current =
            DurableSettlement.Spec.after DurableSettlement.Example.spec 8
              (DurableSettlement.Spec.after DurableSettlement.Example.spec 3
                DurableSettlement.Example.initial) ∧
          scanned.nextSequence = 2 ∧
          scanned.log.entries wire.spec DurableSettlement.Example.initial = [3, 8] := by
  unfold scanJsonPrefix
  rw [show validJson = (Codec.list frameCodec).encode [firstRaw, secondRaw] by rfl]
  rw [(Codec.list frameCodec).decode_encode]
  simp [scanPrefix, scanFramesAux, checkFrame, firstRaw, secondRaw, wire,
    DurableSettlement.Example.spec, DurableSettlement.Example.initial,
    DurableSettlement.Example.entryEffect, DurableSettlement.Spec.after,
    DurableSettlement.Spec.frameDigest, DurableSettlement.Spec.genesisDigest,
    RawFrame.ofFrame, Frame.expected, Log.entries]

theorem frameCodec_rejects_torn :
    frameCodec.decode .null =
      .error (.typeMismatch [] "two-element array" .null) := by
  rfl

theorem scan_noncontiguous_rejected :
    scanPrefix wire DurableSettlement.Example.initial [noncontiguousRaw] =
      .error (.sequenceMismatch 0 4) := by
  rfl

end Example

end Cordis.DurableCodec
