import Cordis.DeepSeekHarnessExtensions
import Cordis.RuntimeRefinement
import Lean.Data.Json.Basic

/-!
# Typed ingress for caller-defined session extensions

`SessionRefinement` deliberately rejects unknown current-Harness event tags.  That is the
source-honest behavior for the deployed event union, but it is not an API for applications that
own a `Session.ExtensionSchema`.  This module supplies the missing boundary without pretending
that JSON can manufacture a dependent payload on its own.

An `ExtensionCodec schema` owns one wire tag and a decoder from its `data` object to the dependent
sum `DecodedExtension schema`.  The generic envelope decoder checks the tag, safe integer sequence
and timestamp fields, and rejects the current-Harness metadata fields that this bounded subset does
not model.  `appendDecodedEvent` then checks that the wire sequence is exactly the session's next
sequence before calling the intrinsically certified `Session.appendLogOnly` or
`Session.appendSurface`.

The example codec accepts a log-only heartbeat and a model-visible banner.  Its exact rejection
witnesses cover wrong tags, ignorable metadata, malformed payloads, and stale sequence numbers.
The codec is a caller-supplied proof boundary; no claim is made about arbitrary JSON, UTF-8,
persistence, deployed provider behavior, or the complete upstream event union.
-/

set_option autoImplicit false

namespace Cordis.SessionExtensionRefinement

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment

/-- Errors specific to the typed extension-ingress boundary. -/
inductive ExtensionDecodeError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | invalidLength (path : List PathSegment) (expected actual : Nat)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | unsupportedField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Nat)
  | sequenceMismatch (path : List PathSegment) (expected actual : Nat)
  deriving BEq, DecidableEq, Repr

/-- One dependent extension event returned by a caller's codec. -/
inductive DecodedExtension (schema : Session.ExtensionSchema) where
  | logOnly (kind : Session.Kind schema .logOnly) (payload : kind.Payload)
  | surface (kind : Session.Kind schema .surface) (payload : kind.Payload)

/-- The wire fields retained after the generic envelope has been checked. -/
structure ExtensionEvent (schema : Session.ExtensionSchema) where
  seq : SafeNat
  time : SafeNat
  extension : DecodedExtension schema

/-- A caller-supplied dependent decoder for one explicit wire event tag. -/
structure ExtensionCodec (schema : Session.ExtensionSchema) where
  typeTag : String
  decodeData : List PathSegment → Lean.Json →
    Except ExtensionDecodeError (DecodedExtension schema)

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def requireField (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except ExtensionDecodeError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def rejectPresent (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except ExtensionDecodeError Unit :=
  if (field? json name).isSome then
    .error (.unsupportedField path name)
  else
    .ok ()

private def decodeString (path : List PathSegment) : Lean.Json →
    Except ExtensionDecodeError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json →
    Except ExtensionDecodeError SafeNat
  | .num ⟨Int.ofNat value, 0⟩ =>
      if safe : value ≤ RuntimeRefinement.maxSafeInteger then
        .ok { value, safe }
      else
        .error (.unsafeInteger path value)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except ExtensionDecodeError String := do
  decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except ExtensionDecodeError SafeNat := do
  decodeSafeNat (fieldPath path name) (← requireField json path name)

private def decodeObjectData (path : List PathSegment) (json : Lean.Json) :
    Except ExtensionDecodeError Unit :=
  match json with
  | .obj _ => .ok ()
  | value => .error (.typeMismatch path "object" (jsonKind value))

/-- Decode the generic current-Harness-shaped envelope for one declared extension tag. -/
def decodeEvent {schema : Session.ExtensionSchema} (codec : ExtensionCodec schema)
    (json : Lean.Json) : Except ExtensionDecodeError (ExtensionEvent schema) := do
  match json with
  | .obj _ => pure ()
  | value => throw (.typeMismatch [] "object" (jsonKind value))
  rejectPresent json [] "ignorable"
  rejectPresent json [] "sourceEventSeqs"
  rejectPresent json [] "surfaceOp"
  let tag ← decodeRequiredString json [] "type"
  if tag = codec.typeTag then
    pure ()
  else
    throw (.unsupportedTag [.field "type"] tag)
  let seq ← decodeRequiredNat json [] "seq"
  let time ← decodeRequiredNat json [] "time"
  let data ← requireField json [] "data"
  let _ ← decodeObjectData [.field "data"] data
  let extension ← codec.decodeData [.field "data"] data
  pure { seq, time, extension }

/-- Append a decoded event once its wire sequence has been proved fresh. -/
def appendDecoded
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema)
    (_seq_eq : event.seq.value = session.nextSeq) :
    Session.Session schema :=
  match event.extension with
  | .logOnly kind payload => session.appendLogOnly kind payload
  | .surface kind payload =>
      session.appendSurface kind payload [] (by simp) (by simp)

/-- Check freshness and append, exposing stale/reordered wire events as a typed error. -/
def appendDecodedEvent
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema) :
    Except ExtensionDecodeError (Session.Session schema) :=
  if h : event.seq.value = session.nextSeq then
    .ok (appendDecoded session event h)
  else
    .error (.sequenceMismatch [.field "seq"] session.nextSeq event.seq.value)

/-- Compose envelope decoding with the exact session-sequence append check. -/
def decodeAndAppend
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (session : Session.Session schema)
    (json : Lean.Json) :
    Except ExtensionDecodeError (Session.Session schema) := do
  let event ← decodeEvent codec json
  appendDecodedEvent session event

@[simp] theorem appendDecoded_nextSeq_core
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema)
    (seq_eq : event.seq.value = session.nextSeq) :
    (appendDecoded session event seq_eq).nextSeq = session.nextSeq + 1 := by
  cases event with
  | mk seq time extension =>
    cases extension <;>
    simp [appendDecoded, Session.Session.appendLogOnly, Session.Session.appendSurface,
      Session.Session.append]

/-- An intrinsic sequential replay of exactly the supplied extension-event AST list. -/
inductive ExtensionReplay
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema) :
    Session.Session schema → List Lean.Json → Session.Session schema → Type where
  | nil (session : Session.Session schema) :
      ExtensionReplay codec session [] session
  | cons
      {before after final : Session.Session schema}
      {raw : Lean.Json}
      {rest : List Lean.Json}
      (event : ExtensionEvent schema)
      (decoded : decodeEvent codec raw = .ok event)
      (appended : appendDecodedEvent before event = .ok after)
      (tail : ExtensionReplay codec after rest final) :
      ExtensionReplay codec before (raw :: rest) final

namespace ExtensionReplay

/-- The typed events extracted from a replay certificate, in source order. -/
def events
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema} :
    {before : Session.Session schema} →
    {input : List Lean.Json} →
    {after : Session.Session schema} →
    ExtensionReplay codec before input after → List (ExtensionEvent schema)
  | _, _, _, .nil _ => []
  | _, _, _, .cons event _ _ tail => event :: tail.events

theorem events_length
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {before after : Session.Session schema}
    {input : List Lean.Json}
    (replay : ExtensionReplay codec before input after) :
    replay.events.length = input.length := by
  induction replay with
  | nil => rfl
  | cons event decoded appended tail tail_ih =>
      simp [events, tail_ih]

theorem raw_length
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {before after : Session.Session schema}
    {input : List Lean.Json}
    (replay : ExtensionReplay codec before input after) :
    input.length = replay.events.length := by
  symm
  exact events_length replay

end ExtensionReplay

theorem appendDecodedEvent_nextSeq
    {schema : Session.ExtensionSchema}
    {session after : Session.Session schema}
    {event : ExtensionEvent schema}
    (appended : appendDecodedEvent session event = .ok after) :
    after.nextSeq = session.nextSeq + 1 := by
  unfold appendDecodedEvent at appended
  split at appended
  · cases appended
    exact appendDecoded_nextSeq_core session event _
  · cases appended

theorem ExtensionReplay.final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {before after : Session.Session schema}
    {input : List Lean.Json}
    (replay : ExtensionReplay codec before input after) :
    after.nextSeq = before.nextSeq + input.length := by
  induction replay with
  | nil => rfl
  | cons event decoded appended tail inductionHypothesis =>
      rw [inductionHypothesis, appendDecodedEvent_nextSeq appended]
      simp only [List.length_cons]
      omega

/-- A validated extension log retains its final indexed session and intrinsic replay proof. -/
structure ValidatedExtensionLog
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) where
  final : Session.Session schema
  replay : ExtensionReplay codec initial input final

namespace ValidatedExtensionLog

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (log : ValidatedExtensionLog codec initial input) :
    log.final.nextSeq = initial.nextSeq + input.length :=
  log.replay.final_nextSeq

theorem typed_event_count
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (log : ValidatedExtensionLog codec initial input) :
    log.replay.events.length = input.length :=
  log.replay.events_length

end ValidatedExtensionLog

private def validateAt
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (session : Session.Session schema) :
    (input : List Lean.Json) →
    Except ExtensionDecodeError (ValidatedExtensionLog codec session input)
  | [] => .ok { final := session, replay := .nil session }
  | raw :: rest =>
      match decodedResult : decodeEvent codec raw with
      | .error error => .error error
      | .ok event =>
          match appendedResult : appendDecodedEvent session event with
          | .error error => .error error
          | .ok after =>
              match _tailResult : validateAt codec after rest with
              | .error error => .error error
              | .ok tail =>
                  .ok {
                    final := tail.final
                    replay := .cons event decodedResult appendedResult tail.replay
                  }

/-- Validate and replay an ordered extension-event AST list from one certified session. -/
def validate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) :
    Except ExtensionDecodeError (ValidatedExtensionLog codec initial input) :=
  validateAt codec initial input

@[simp] theorem appendDecoded_nextSeq
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema)
    (seq_eq : event.seq.value = session.nextSeq) :
    (appendDecoded session event seq_eq).nextSeq = session.nextSeq + 1 := by
  cases event with
  | mk seq time extension =>
    cases extension <;>
    simp [appendDecoded, Session.Session.appendLogOnly, Session.Session.appendSurface,
      Session.Session.append]

@[simp] theorem appendDecoded_event_count
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema)
    (seq_eq : event.seq.value = session.nextSeq) :
    (appendDecoded session event seq_eq).events.length = session.events.length + 1 := by
  cases event with
  | mk seq time extension =>
    cases extension <;>
    simp [appendDecoded, Session.Session.appendLogOnly, Session.Session.appendSurface,
      Session.Session.append]

theorem appendDecoded_wire_seq
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (event : ExtensionEvent schema)
    (seq_eq : event.seq.value = session.nextSeq) :
    event.seq.value = (appendDecoded session event seq_eq).nextSeq - 1 := by
  rw [appendDecoded_nextSeq]
  omega

namespace Example

open DeepSeekHarnessExtensions

private def dataPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def exampleCodecDecode (path : List PathSegment) (json : Lean.Json) :
    Except ExtensionDecodeError (DecodedExtension exampleSchema) := do
  let _ ← decodeObjectData path json
  let kind ← decodeRequiredString json path "kind"
  match kind with
  | "heartbeat" =>
      rejectPresent json path "text"
      .ok (.logOnly (.custom ExampleKind.heartbeat) .heartbeat)
  | "banner" =>
      let text ← decodeRequiredString json path "text"
      .ok (.surface (.custom ExampleKind.banner) (.banner text))
  | tag => .error (.unsupportedTag (dataPath path "kind") tag)

def exampleCodec : ExtensionCodec exampleSchema where
  typeTag := "cordis/extension"
  decodeData := exampleCodecDecode

def heartbeatJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

def bannerJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 101)),
  ("data", Lean.Json.mkObj [
    ("kind", .str "banner"),
    ("text", .str "ready")
  ])
]

def bannerAfterHeartbeatJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 1)),
  ("time", .num (Lean.JsonNumber.fromNat 102)),
  ("data", Lean.Json.mkObj [
    ("kind", .str "banner"),
    ("text", .str "ready")
  ])
]

def exampleInput : List Lean.Json := [heartbeatJson, bannerAfterHeartbeatJson]

def validatedExample :
    Except ExtensionDecodeError
      (ValidatedExtensionLog exampleCodec (Session.Session.empty exampleSchema) exampleInput) :=
  validate exampleCodec (Session.Session.empty exampleSchema) exampleInput

def wrongTagJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "session/turn-start"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

def ignorableJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("ignorable", .bool true),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

def malformedBannerJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 101)),
  ("data", Lean.Json.mkObj [("kind", .str "banner"), ("text", .num 3)])
]

def staleHeartbeatJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 1)),
  ("time", .num (Lean.JsonNumber.fromNat 102)),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

def heartbeatSession : Except ExtensionDecodeError (Session.Session exampleSchema) :=
  decodeAndAppend exampleCodec (Session.Session.empty exampleSchema) heartbeatJson

def bannerSession : Except ExtensionDecodeError (Session.Session exampleSchema) :=
  decodeAndAppend exampleCodec (Session.Session.empty exampleSchema) bannerJson

theorem decode_heartbeat_exact :
    decodeEvent exampleCodec heartbeatJson = .ok {
      seq := { value := 0, safe := by decide }
      time := { value := 100, safe := by decide }
      extension := .logOnly (.custom ExampleKind.heartbeat) .heartbeat
    } := by
  rfl

theorem decode_banner_exact :
    decodeEvent exampleCodec bannerJson = .ok {
      seq := { value := 0, safe := by decide }
      time := { value := 101, safe := by decide }
      extension := .surface (.custom ExampleKind.banner) (.banner "ready")
    } := by
  rfl

theorem heartbeat_append_exact :
    heartbeatSession = .ok ((Session.Session.empty exampleSchema).appendLogOnly
      (.custom ExampleKind.heartbeat) .heartbeat) := by
  rfl

theorem banner_append_messages :
    bannerSession.map Session.Session.messages =
      .ok [.user "extension:ready"] := by
  rfl

theorem validated_example_summary :
    (match validatedExample with
    | .error _ => none
    | .ok log => some (log.final.nextSeq, log.final.messages, log.replay.events.length)) =
      some (2, [.user "extension:ready"], 2) := by
  rfl

theorem reject_wrong_tag :
    decodeEvent exampleCodec wrongTagJson =
      .error (.unsupportedTag [.field "type"] "session/turn-start") := by
  rfl

theorem reject_ignorable :
    decodeEvent exampleCodec ignorableJson =
      .error (.unsupportedField [] "ignorable") := by
  rfl

theorem reject_malformed_banner :
    decodeEvent exampleCodec malformedBannerJson =
      .error (.typeMismatch [.field "data", .field "text"] "string" .number) := by
  rfl

theorem reject_stale_sequence :
    decodeAndAppend exampleCodec (Session.Session.empty exampleSchema) staleHeartbeatJson =
      .error (.sequenceMismatch [.field "seq"] 0 1) := by
  rfl

end Example

end Cordis.SessionExtensionRefinement
