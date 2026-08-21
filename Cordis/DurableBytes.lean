import Cordis.DurableCodec

/-!
# Pure byte framing for durable prefixes

`DurableCodec` validates a list of `Lean.Json` values and then constructs an exact
typed settlement log.  This module adds the next, deliberately smaller boundary:
an executable binary framing layer over `List UInt8`.  A frame is encoded as a
unary byte length (zero bytes followed by a one byte delimiter) and an explicitly
supplied payload codec.  The parser rejects an invalid length prefix, a truncated
payload, and a payload rejected by that codec.

The framing theorem is independent of JSON rendering, UTF-8, files, `fsync`, or
cryptographic digests.  `rawFramePayloadCodec` is a compact binary codec for the
numeric `RawFrame` representation; it is a Lean witness for this format, not a
claim that the TypeScript Harness uses the same bytes.  `scanBytesPrefix` accepts
a frame count as a crash-prefix certificate, exposes any unconsumed torn suffix,
and delegates semantic validation to `DurableCodec.scanPrefix`.
-/

namespace Cordis.DurableBytes

open Cordis
open Cordis.DurableCodec
open Cordis.DurableSettlement

universe u v

set_option autoImplicit false

/-! ## Framing primitives -/

/-- A pure finite byte sequence used by this module's binary format. -/
abbrev Bytes := List UInt8

/-- Read a unary length prefix and return its length together with the suffix. -/
def readLength : Bytes → Option (Nat × Bytes)
  | [] => none
  | byte :: rest =>
      if byte = 0 then
        match readLength rest with
        | none => none
        | some (length, suffix) => some (length + 1, suffix)
      else if byte = 1 then
        some (0, rest)
      else none
termination_by bytes => bytes.length

/-- Encode a natural number as zero repeated `value` times followed by delimiter `1`. -/
def encodeNat (value : Nat) : Bytes := List.replicate value 0 ++ [1]

theorem readLength_encodeNat (value : Nat) (suffix : Bytes) :
    readLength (encodeNat value ++ suffix) = some (value, suffix) := by
  induction value generalizing suffix with
  | zero => simp [encodeNat, readLength]
  | succ value ih =>
      simp only [encodeNat, List.replicate_succ, List.cons_append]
      simp only [readLength]
      have h : readLength (List.replicate value 0 ++ [1] ++ suffix) =
          some (value, suffix) := by
        rw [show List.replicate value 0 ++ [1] ++ suffix = encodeNat value ++ suffix by
          simp [encodeNat, List.append_assoc]]
        exact ih suffix
      rw [h]
      rfl

/-- Take exactly `count` bytes, failing when the input is too short. -/
def takeExact : Nat → Bytes → Option (Bytes × Bytes)
  | 0, bytes => some ([], bytes)
  | _ + 1, [] => none
  | count + 1, byte :: rest =>
      match takeExact count rest with
      | none => none
      | some (payload, suffix) => some (byte :: payload, suffix)

theorem takeExact_append (payload suffix : Bytes) :
    takeExact payload.length (payload ++ suffix) = some (payload, suffix) := by
  induction payload with
  | nil => simp [takeExact]
  | cons head tail ih =>
      simp [takeExact, ih]

/-! ## Payload codecs and one-frame decoding -/

/-- A binary payload codec with its in-memory round-trip law. -/
structure PayloadCodec (alpha : Type u) where
  encode : alpha → Bytes
  decode : Bytes → Except String alpha
  roundtrip : ∀ value, decode (encode value) = .ok value

/-- Errors separated by the framing layer before semantic durable validation. -/
inductive ByteFrameError where
  | malformedLength
  | truncatedPayload (expected actual : Nat)
  | payloadError (message : String)
deriving Repr

/-- Prefix one payload with its unary byte length. -/
def encodeFrame {alpha : Type u} (codec : PayloadCodec alpha) (value : alpha) : Bytes :=
  encodeNat (codec.encode value).length ++ codec.encode value

/-- Decode one framed payload and return any bytes after that frame. -/
def decodeFrame {alpha : Type u} (codec : PayloadCodec alpha) (bytes : Bytes) :
    Except ByteFrameError (alpha × Bytes) :=
  match readLength bytes with
  | none => .error .malformedLength
  | some (length, rest) =>
      match takeExact length rest with
      | none => .error (.truncatedPayload length rest.length)
      | some (payload, suffix) =>
          match codec.decode payload with
          | .error message => .error (.payloadError message)
          | .ok value => .ok (value, suffix)

theorem decodeFrame_encode {alpha : Type u} (codec : PayloadCodec alpha) (value : alpha)
    (suffix : Bytes) :
    decodeFrame codec (encodeFrame codec value ++ suffix) = .ok (value, suffix) := by
  simp only [decodeFrame, encodeFrame]
  rw [show encodeNat (codec.encode value).length ++ codec.encode value ++ suffix =
      encodeNat (codec.encode value).length ++ (codec.encode value ++ suffix) by
    simp [List.append_assoc]]
  rw [readLength_encodeNat]
  simp [takeExact_append, codec.roundtrip]

/-! ## Counted frame prefixes -/

/-- Encode a chronological list of payloads without adding an external terminator. -/
def encodeMany {alpha : Type u} (codec : PayloadCodec alpha) : List alpha → Bytes
  | [] => []
  | value :: values => encodeFrame codec value ++ encodeMany codec values

/-- Decode exactly `count` frames, retaining the unconsumed suffix. -/
def decodeFrames {alpha : Type u} (codec : PayloadCodec alpha) : Nat → Bytes →
    Except ByteFrameError (List alpha × Bytes)
  | 0, bytes => .ok ([], bytes)
  | count + 1, bytes =>
      match decodeFrame codec bytes with
      | .error error => .error error
      | .ok (value, suffix) =>
          match decodeFrames codec count suffix with
          | .error error => .error error
          | .ok (values, rest) => .ok (value :: values, rest)

theorem decodeFrames_encodeMany {alpha : Type u} (codec : PayloadCodec alpha)
    (values : List alpha) (suffix : Bytes) :
    decodeFrames codec values.length (encodeMany codec values ++ suffix) =
      .ok (values, suffix) := by
  induction values with
  | nil => simp [encodeMany, decodeFrames]
  | cons head tail ih =>
      simp only [List.length_cons, encodeMany, decodeFrames]
      rw [show encodeFrame codec head ++ encodeMany codec tail ++ suffix =
          encodeFrame codec head ++ (encodeMany codec tail ++ suffix) by
        simp [List.append_assoc]]
      rw [decodeFrame_encode]
      simp only [ih]

theorem decodeFrames_encodeMany_exact {alpha : Type u} (codec : PayloadCodec alpha)
    (values : List alpha) :
    decodeFrames codec values.length (encodeMany codec values) = .ok (values, []) := by
  simpa using decodeFrames_encodeMany codec values []

/-! ## A compact binary codec for `RawFrame` -/

/-- Parse exactly `count` unary natural numbers from a byte suffix. -/
def parseNats : Nat → Bytes → Option (List Nat × Bytes)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (value, rest) ← readLength bytes
      let (values, suffix) ← parseNats count rest
      return (value :: values, suffix)

theorem parseNats_encode (values : List Nat) (suffix : Bytes) :
    parseNats values.length (values.flatMap encodeNat ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => simp [parseNats]
  | cons head tail ih =>
      simp only [List.length_cons, List.flatMap_cons]
      rw [List.append_assoc]
      simp only [parseNats, readLength_encodeNat]
      simp [ih]

/-- Encode a digest by first recording its number of natural entries. -/
def encodeNatList (values : List Nat) : Bytes :=
  encodeNat values.length ++ values.flatMap encodeNat

/-- Decode the count-prefixed unary natural list used for a digest. -/
def decodeNatList (bytes : Bytes) : Option (List Nat × Bytes) := do
  let (count, rest) ← readLength bytes
  parseNats count rest

theorem decodeNatList_encode (values : List Nat) (suffix : Bytes) :
    decodeNatList (encodeNatList values ++ suffix) = some (values, suffix) := by
  simp only [decodeNatList, encodeNatList]
  rw [show encodeNat values.length ++ values.flatMap encodeNat ++ suffix =
      encodeNat values.length ++ (values.flatMap encodeNat ++ suffix) by
    simp [List.append_assoc]]
  rw [readLength_encodeNat]
  simpa using parseNats_encode values suffix

def encodeDigest (values : Digest) : Bytes := encodeNatList values

def decodeDigest (bytes : Bytes) : Option (Digest × Bytes) := decodeNatList bytes

theorem decodeDigest_encode (values : Digest) (suffix : Bytes) :
    decodeDigest (encodeDigest values ++ suffix) = some (values, suffix) := by
  exact decodeNatList_encode values suffix

/-- Encode all numeric fields of a raw durable frame in a fixed field order. -/
def encodeRawFrame (frame : RawFrame) : Bytes :=
  encodeNat frame.sequence ++ encodeDigest frame.previous ++
    encodeNat frame.entryCode ++ encodeNat frame.afterCode ++ encodeDigest frame.digest

/-- Decode a raw frame while retaining bytes after its five fields. -/
def decodeRawFrameWithSuffix (bytes : Bytes) : Option (RawFrame × Bytes) := do
  let (sequence, rest) ← readLength bytes
  let (previous, rest) ← decodeDigest rest
  let (entryCode, rest) ← readLength rest
  let (afterCode, rest) ← readLength rest
  let (digest, suffix) ← decodeDigest rest
  return ({ sequence, previous, entryCode, afterCode, digest }, suffix)

theorem decodeRawFrameWithSuffix_encode (frame : RawFrame) (suffix : Bytes) :
    decodeRawFrameWithSuffix (encodeRawFrame frame ++ suffix) = some (frame, suffix) := by
  cases frame with
  | mk sequence previous entryCode afterCode digest =>
      simp [encodeRawFrame, decodeRawFrameWithSuffix, List.append_assoc,
        readLength_encodeNat, decodeDigest_encode]

/-- Reject malformed or non-exhaustive raw-frame payloads. -/
def decodeRawFrame (bytes : Bytes) : Except String RawFrame :=
  match decodeRawFrameWithSuffix bytes with
  | none => .error "malformed raw frame"
  | some (frame, []) => .ok frame
  | some (_, _ :: _) => .error "trailing raw frame bytes"

theorem decodeRawFrame_encode (frame : RawFrame) :
    decodeRawFrame (encodeRawFrame frame) = .ok frame := by
  unfold decodeRawFrame
  have h : decodeRawFrameWithSuffix (encodeRawFrame frame) = some (frame, []) := by
    simpa using decodeRawFrameWithSuffix_encode frame []
  rw [h]

/-- The concrete numeric raw-frame payload codec used by the byte examples. -/
def rawFramePayloadCodec : PayloadCodec RawFrame where
  encode := encodeRawFrame
  decode := decodeRawFrame
  roundtrip := decodeRawFrame_encode

/-! ## Durable semantic prefix bridge -/

inductive ScanBytesError where
  | framing (error : ByteFrameError)
  | semantic (error : ScanError)
deriving Repr

/-- A decoded typed settlement prefix plus bytes discarded after its crash cut. -/
def scanBytesPrefix
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State)
    (codec : PayloadCodec RawFrame) (count : Nat) (bytes : Bytes) :
    Except ScanBytesError (ScannedLog wire initial × Bytes) :=
  match decodeFrames codec count bytes with
  | .error error => .error (.framing error)
  | .ok (raw, suffix) =>
      match scanPrefix wire initial raw with
      | .error error => .error (.semantic error)
      | .ok scanned => .ok (scanned, suffix)

theorem scanBytesPrefix_encode
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State)
    (codec : PayloadCodec RawFrame) (raw : List RawFrame) (suffix : Bytes)
    {scanned : ScannedLog wire initial}
    (h : scanPrefix wire initial raw = .ok scanned) :
    scanBytesPrefix wire initial codec raw.length
      (encodeMany codec raw ++ suffix) = .ok (scanned, suffix) := by
  simp [scanBytesPrefix, decodeFrames_encodeMany, h]

/-! ## Exact executable examples -/

namespace Example

open Cordis.DurableCodec.Example

def firstBytes : Bytes := encodeFrame rawFramePayloadCodec firstRaw

def secondBytes : Bytes := encodeFrame rawFramePayloadCodec secondRaw

def validBytes : Bytes := encodeMany rawFramePayloadCodec [firstRaw, secondRaw]

def tornBytes : Bytes := validBytes ++ [0]

theorem rawFrame_bytes_roundtrip :
    decodeFrame rawFramePayloadCodec (firstBytes ++ secondBytes) =
      .ok (firstRaw, secondBytes) := by
  exact decodeFrame_encode rawFramePayloadCodec firstRaw secondBytes

theorem valid_bytes_decode :
    decodeFrames rawFramePayloadCodec 2 validBytes = .ok ([firstRaw, secondRaw], []) := by
  exact decodeFrames_encodeMany_exact rawFramePayloadCodec [firstRaw, secondRaw]

theorem torn_bytes_rejected :
    ∃ error, decodeFrames rawFramePayloadCodec 3 tornBytes = .error error := by
  refine ⟨.malformedLength, ?_⟩
  simp only [tornBytes, decodeFrames, validBytes, encodeMany]
  rw [show encodeFrame rawFramePayloadCodec firstRaw ++
      (encodeFrame rawFramePayloadCodec secondRaw ++ []) ++ [0] =
      encodeFrame rawFramePayloadCodec firstRaw ++
        (encodeFrame rawFramePayloadCodec secondRaw ++ [0]) by
    simp [List.append_assoc]]
  rw [decodeFrame_encode]
  simp
  rw [decodeFrame_encode]
  simp [decodeFrame, readLength]

theorem valid_bytes_scan :
    scanBytesPrefix wire DurableSettlement.Example.initial rawFramePayloadCodec 2 validBytes =
      .ok ({
        current :=
          DurableSettlement.Spec.after DurableSettlement.Example.spec 8
            (DurableSettlement.Spec.after DurableSettlement.Example.spec 3
              DurableSettlement.Example.initial)
        nextSequence := 2
        digest :=
          DurableSettlement.Spec.frameDigest
            DurableSettlement.Example.spec
            (DurableSettlement.Spec.frameDigest
              DurableSettlement.Example.spec
              DurableSettlement.Example.spec.genesisDigest 0 3 13)
            1 8 21
        log := DurableSettlement.Example.second
      }, []) := by
  have h := scanBytesPrefix_encode wire DurableSettlement.Example.initial
    rawFramePayloadCodec [firstRaw, secondRaw] []
    (scanned := {
      current :=
        DurableSettlement.Spec.after DurableSettlement.Example.spec 8
          (DurableSettlement.Spec.after DurableSettlement.Example.spec 3
            DurableSettlement.Example.initial)
      nextSequence := 2
      digest :=
        DurableSettlement.Spec.frameDigest
          DurableSettlement.Example.spec
          (DurableSettlement.Spec.frameDigest
            DurableSettlement.Example.spec
            DurableSettlement.Example.spec.genesisDigest 0 3 13)
          1 8 21
      log := DurableSettlement.Example.second
    }) (by rfl)
  simpa [validBytes] using h

end Example

end Cordis.DurableBytes
