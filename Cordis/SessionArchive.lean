import Cordis.SessionRefinement

/-!
# Lossless archive boundary for current Harness session envelopes

The pinned DeepSeek Harness session format is merge-extensible: an event envelope carries
`type`, `seq`, `time`, and arbitrary JSON `data`, while `ignorable`, `sourceEventSeqs`, and
`surfaceOp` are conditional envelope fields. `SessionRefinement` intentionally validates a
smaller semantic subset and therefore rejects unknown or unsupported records.

This module closes the adjacent, source-honest persistence boundary. It validates the envelope
shape while retaining the original JSON AST exactly. A known supported event is accompanied by
the existing typed `WireEvent` decoder certificate. An unknown or semantically unsupported event
is retained as opaque; an absent `ignorable` marker makes it `opaqueRequired`, while an explicit
`true` marker makes it `opaqueIgnorable`. Required opaque records are never silently dropped.

The archive is not a semantic session replay theorem. It does not invent payload types for
extension events, image/tool-result blocks, replay metadata, or future plugin records. The exact
raw AST, envelope metadata, order, and supported-event certificates are the proof boundary; a
caller that wants to resume or reconstruct a local `Session` must still discharge the semantic
obligations for every required opaque record.
-/

set_option autoImplicit false

namespace Cordis.SessionArchive

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev SurfaceOp := SessionRefinement.WireSurfaceOp

/-- Envelope-level failures. Payload JSON is deliberately not decoded here. -/
inductive ArchiveError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Nat)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | malformed (path : List PathSegment) (message : String)
  deriving BEq, DecidableEq, Repr

/-- All envelope fields needed to classify a raw event. `raw` is the exact source AST. -/
structure Envelope where
  raw : Lean.Json
  type : String
  seq : SafeNat
  time : SafeNat
  data : Lean.Json
  ignorable : Option Bool
  sourceEventSeqs : Option (List SafeNat)
  surfaceOp : Option SurfaceOp

private structure EnvelopeFields where
  type : String
  seq : SafeNat
  time : SafeNat
  data : Lean.Json
  ignorable : Option Bool
  sourceEventSeqs : Option (List SafeNat)
  surfaceOp : Option SurfaceOp

namespace Envelope

/-- The source contract only admits the literal `true` marker when `ignorable` is present. -/
def isIgnorable (envelope : Envelope) : Bool := envelope.ignorable == some true

theorem isIgnorable_iff (envelope : Envelope) :
    envelope.isIgnorable = true ↔ envelope.ignorable = some true := by
  simp [isIgnorable]

end Envelope

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def indexPath (path : List PathSegment) (index : Nat) : List PathSegment :=
  path ++ [.index index]

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def requireField (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ArchiveError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def decodeString (path : List PathSegment) : Lean.Json → Except ArchiveError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json → Except ArchiveError SafeNat
  | .num ⟨Int.ofNat value, 0⟩ =>
      if safe : value ≤ RuntimeRefinement.maxSafeInteger then
        .ok { value, safe }
      else
        .error (.unsafeInteger path value)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ArchiveError String := do
  decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ArchiveError SafeNat := do
  decodeSafeNat (fieldPath path name) (← requireField json path name)

private def decodeOptionalBool (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ArchiveError (Option Bool) :=
  match field? json name with
  | none => .ok none
  | some (.bool value) =>
      if value then
        .ok (some true)
      else
        .error (.malformed (fieldPath path name) "the source marker must be true when present")
  | some value => .error (.typeMismatch (fieldPath path name) "boolean" (jsonKind value))

private def decodeSafeNatList (path : List PathSegment) : Lean.Json →
    Except ArchiveError (List SafeNat)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except ArchiveError (List SafeNat)
        | _, [] => .ok []
        | index, value :: rest => do
            let head ← decodeSafeNat (indexPath path index) value
            let tail ← loop (index + 1) rest
            .ok (head :: tail)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array of nonnegative safe integers" (jsonKind json))

private def decodeOptionalSafeNatList (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except ArchiveError (Option (List SafeNat)) :=
  match field? json name with
  | none => .ok none
  | some value => some <$> decodeSafeNatList (fieldPath path name) value

private def decodeSurfaceOp (path : List PathSegment) : Lean.Json → Except ArchiveError SurfaceOp
  | .str "append" => .ok .append
  | .str tag => .error (.unsupportedTag path tag)
  | json@(.obj _) => do
      let operation ← decodeRequiredString json path "op"
      let operationPath := fieldPath path "op"
      if operation != "replace" then
        throw (.unsupportedTag operationPath operation)
      let start ← decodeRequiredNat json path "start"
      let endSeq ← decodeRequiredNat json path "end"
      .ok (.replace start endSeq)
  | json => .error (.typeMismatch path "string or object" (jsonKind json))

private def decodeOptionalSurfaceOp (json : Lean.Json) (path : List PathSegment) :
    Except ArchiveError (Option SurfaceOp) :=
  match field? json "surfaceOp" with
  | none => .ok none
  | some value => some <$> decodeSurfaceOp (fieldPath path "surfaceOp") value

private def decodeEnvelopeFieldsAt (path : List PathSegment) (json : Lean.Json) :
    Except ArchiveError EnvelopeFields := do
  match json with
  | .obj _ => pure ()
  | value => throw (.typeMismatch path "object" (jsonKind value))
  let type ← decodeRequiredString json path "type"
  let seq ← decodeRequiredNat json path "seq"
  let time ← decodeRequiredNat json path "time"
  let data ← requireField json path "data"
  let ignorable ← decodeOptionalBool json path "ignorable"
  let sourceEventSeqs ← decodeOptionalSafeNatList json path "sourceEventSeqs"
  let surfaceOp ← decodeOptionalSurfaceOp json path
  .ok { type, seq, time, data, ignorable, sourceEventSeqs, surfaceOp }

private def decodeEnvelopeAt (path : List PathSegment) (json : Lean.Json) :
    Except ArchiveError Envelope := do
  let fields ← decodeEnvelopeFieldsAt path json
  .ok {
    raw := json
    type := fields.type
    seq := fields.seq
    time := fields.time
    data := fields.data
    ignorable := fields.ignorable
    sourceEventSeqs := fields.sourceEventSeqs
    surfaceOp := fields.surfaceOp
  }

private theorem decodeEnvelopeAt_raw (path : List PathSegment) (json : Lean.Json)
    (envelope : Envelope) (h : decodeEnvelopeAt path json = .ok envelope) :
    envelope.raw = json := by
  unfold decodeEnvelopeAt at h
  cases parsed : decodeEnvelopeFieldsAt path json with
  | error error =>
      rw [parsed] at h
      change Except.error error = .ok envelope at h
      cases h
  | ok fields =>
      rw [parsed] at h
      cases h
      rfl

/-- Parse one envelope, retaining the exact original JSON AST in the result. -/
def decodeEnvelope (json : Lean.Json) : Except ArchiveError Envelope :=
  decodeEnvelopeAt [] json

/-- Parse one envelope under a caller-supplied JSON path, preserving indexed diagnostics. -/
def decodeEnvelopeAtPath (path : List PathSegment) (json : Lean.Json) :
    Except ArchiveError Envelope :=
  decodeEnvelopeAt path json

theorem decodeEnvelopeAtPath_raw (path : List PathSegment) (json : Lean.Json)
    (envelope : Envelope) (h : decodeEnvelopeAtPath path json = .ok envelope) :
    envelope.raw = json := by
  exact decodeEnvelopeAt_raw path json envelope h

private def decodeEnvelopesAt : Nat → List Lean.Json → Except ArchiveError (List Envelope)
  | _, [] => .ok []
  | index, json :: rest => do
      let head ← decodeEnvelopeAt [.index index] json
      let tail ← decodeEnvelopesAt (index + 1) rest
      .ok (head :: tail)

/-- Parse an ordered list of valid Harness envelopes with element-indexed errors. -/
def decodeEnvelopes (json : List Lean.Json) : Except ArchiveError (List Envelope) :=
  decodeEnvelopesAt 0 json

theorem decodeEnvelope_raw (json : Lean.Json) (envelope : Envelope)
    (h : decodeEnvelope json = .ok envelope) : envelope.raw = json := by
  exact decodeEnvelopeAt_raw [] json envelope h

/-- A supported event retains the typed semantic certificate from `SessionRefinement`. -/
structure Supported where
  envelope : Envelope
  event : SessionRefinement.WireEvent
  decoded : SessionRefinement.decodeEvent envelope.raw = .ok event

/-- Classification of one syntactically valid envelope. -/
inductive ArchivedEvent where
  | supported (certificate : Supported)
  | opaqueRequired (envelope : Envelope)
  | opaqueIgnorable (envelope : Envelope)

namespace ArchivedEvent

def envelope : ArchivedEvent → Envelope
  | .supported certificate => certificate.envelope
  | .opaqueRequired envelope => envelope
  | .opaqueIgnorable envelope => envelope

def raw (event : ArchivedEvent) : Lean.Json := event.envelope.raw

def isOpaque : ArchivedEvent → Bool
  | .supported _ => false
  | .opaqueRequired _ => true
  | .opaqueIgnorable _ => true

def isRequired : ArchivedEvent → Bool
  | .supported _ => false
  | .opaqueRequired _ => true
  | .opaqueIgnorable _ => false

theorem raw_eq_envelope_raw (event : ArchivedEvent) : event.raw = event.envelope.raw := rfl

end ArchivedEvent

/-- Classify a parsed envelope by delegating supported payloads to the semantic decoder. -/
def classify (envelope : Envelope) : ArchivedEvent :=
  match h : SessionRefinement.decodeEvent envelope.raw with
  | .ok event => .supported { envelope, event, decoded := h }
  | .error _ =>
      if envelope.isIgnorable then
        .opaqueIgnorable envelope
      else
        .opaqueRequired envelope

/-- Full archive result, retaining both input order and classified records. -/
structure ArchivedLog (input : List Lean.Json) where
  events : List ArchivedEvent
  length_eq : events.length = input.length
  raw_eq : events.map ArchivedEvent.raw = input

private def classifyEnvelopes : List Envelope → List ArchivedEvent
  | [] => []
  | envelope :: rest => classify envelope :: classifyEnvelopes rest

theorem classify_raw (envelope : Envelope) :
    (classify envelope).raw = envelope.raw := by
  unfold classify
  split
  · rfl
  · split <;> rfl

private theorem classifyEnvelopes_length (envelopes : List Envelope) :
    (classifyEnvelopes envelopes).length = envelopes.length := by
  induction envelopes with
  | nil => rfl
  | cons head tail ih => simp [classifyEnvelopes, ih]

private theorem classifyEnvelopes_raw (envelopes : List Envelope) :
    (classifyEnvelopes envelopes).map ArchivedEvent.raw = envelopes.map Envelope.raw := by
  induction envelopes with
  | nil => rfl
  | cons head tail ih =>
      have headRaw : (classify head).raw = head.raw := classify_raw head
      simp [classifyEnvelopes, headRaw, ih]

 /-- Decode and classify an ordered archive without discarding an opaque record. -/
private def archiveAt : (index : Nat) → (input : List Lean.Json) →
    Except ArchiveError (ArchivedLog input)
  | _, [] => .ok { events := [], length_eq := rfl, raw_eq := rfl }
  | index, json :: rest =>
      match envelopeResult : decodeEnvelopeAt [.index index] json with
      | .error error => .error error
      | .ok envelope =>
          match tailResult : archiveAt (index + 1) rest with
          | .error error => .error error
          | .ok tail =>
              let head := classify envelope
              .ok {
                events := head :: tail.events
                length_eq := by simp [tail.length_eq]
                raw_eq := by
                  have envelopeRaw := decodeEnvelopeAt_raw [.index index] json envelope envelopeResult
                  have rawHead : head.raw = json := by
                    simpa [head] using (classify_raw envelope).trans envelopeRaw
                  simp [rawHead, tail.raw_eq]
              }

def archive (input : List Lean.Json) : Except ArchiveError (ArchivedLog input) :=
  archiveAt 0 input

/-- A small supported core record used by the executable archive witness. -/
def supportedTurnStartJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 100),
  ("data", Lean.Json.mkObj [("turn", .num 1)])
]

/-- A required extension record: it is retained, but no local payload is guessed. -/
def requiredExtensionJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/future-event"), ("seq", .num 1), ("time", .num 101),
  ("data", Lean.Json.mkObj [("opaque", .str "preserve-me")]),
  ("providerExtension", Lean.Json.mkObj [("revision", .num 4)])
]

/-- An explicitly ignorable extension record: it is still retained in the archive. -/
def ignorableExtensionJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/telemetry"), ("seq", .num 2), ("time", .num 102),
  ("data", Lean.Json.mkObj [("sample", .num 7)]), ("ignorable", .bool true)
]

def archiveExampleJson : List Lean.Json :=
  [supportedTurnStartJson, requiredExtensionJson, ignorableExtensionJson]

def classificationTag : ArchivedEvent → String
  | .supported _ => "supported"
  | .opaqueRequired _ => "opaque-required"
  | .opaqueIgnorable _ => "opaque-ignorable"

def archiveTags (input : List Lean.Json) : List String :=
  match archive input with
  | .error _ => []
  | .ok log => log.events.map classificationTag

theorem archive_example_tags :
    archiveTags archiveExampleJson =
      ["supported", "opaque-required", "opaque-ignorable"] := by
  rfl

theorem archive_example_raw_preserved :
    (match archive archiveExampleJson with
    | .error _ => []
    | .ok log => log.events.map ArchivedEvent.raw) = archiveExampleJson := by
  rfl

end Cordis.SessionArchive
