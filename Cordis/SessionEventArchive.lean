import Cordis.SessionArchive

/-!
# Full current-Harness event-tag archive

`SessionRefinement` intentionally accepts a semantic subset of the pinned Harness
`SessionEvent` union.  `SessionArchive` already keeps an unsupported envelope losslessly, but
does not distinguish an unsupported *known* core event from an extension event.  This module
moves that wire boundary inward without guessing payload semantics: it recognizes every core
event tag in the pinned union, requires its `data` to be an object, rejects surface metadata on
log-only tags, delegates the supported subset to `SessionRefinement`, and keeps every other
known payload as a typed opaque record with its exact source AST.

The result is a wire/tag coverage certificate, not a full event-payload decoder.  In particular,
assistant message blocks, provider usage/failure objects, tool-result `error`/`meta`, future
request configuration, extension records, replay behavior, timestamps, persistence durability,
and whole-session equivalence remain outside this layer.
-/

set_option autoImplicit false

namespace Cordis.SessionEventArchive

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev Envelope := SessionArchive.Envelope

/-- The complete pinned core `SessionEventMap` tag family (extensions are not included). -/
inductive KnownTag where
  | turnStart
  | turnEnd
  | stepStart
  | stepEnd
  | userMessage
  | assistantChunk
  | assistantMessage
  | toolCall
  | toolResult
  | todoWrite
  | requestHeader
  | requestContext
  | sessionEndSeed
  deriving BEq, DecidableEq, Repr

namespace KnownTag

def wire : KnownTag → String
  | .turnStart => "turn/start"
  | .turnEnd => "turn/end"
  | .stepStart => "step/start"
  | .stepEnd => "step/end"
  | .userMessage => "user/message"
  | .assistantChunk => "assistant/chunk"
  | .assistantMessage => "assistant/message"
  | .toolCall => "tool/call"
  | .toolResult => "tool/result"
  | .todoWrite => "todo/write"
  | .requestHeader => "request/header"
  | .requestContext => "request/context"
  | .sessionEndSeed => "session/end-seed"

def fromString : String → Option KnownTag
  | "turn/start" => some .turnStart
  | "turn/end" => some .turnEnd
  | "step/start" => some .stepStart
  | "step/end" => some .stepEnd
  | "user/message" => some .userMessage
  | "assistant/chunk" => some .assistantChunk
  | "assistant/message" => some .assistantMessage
  | "tool/call" => some .toolCall
  | "tool/result" => some .toolResult
  | "todo/write" => some .todoWrite
  | "request/header" => some .requestHeader
  | "request/context" => some .requestContext
  | "session/end-seed" => some .sessionEndSeed
  | _ => none

def all : List KnownTag :=
  [.turnStart, .turnEnd, .stepStart, .stepEnd, .userMessage, .assistantChunk,
    .assistantMessage, .toolCall, .toolResult, .todoWrite, .requestHeader,
    .requestContext, .sessionEndSeed]

def isSurface : KnownTag → Bool
  | .userMessage | .assistantMessage | .toolResult => true
  | _ => false

theorem all_length : all.length = 13 := by
  rfl

theorem all_wires : all.map wire =
    ["turn/start", "turn/end", "step/start", "step/end", "user/message",
      "assistant/chunk", "assistant/message", "tool/call", "tool/result", "todo/write",
      "request/header", "request/context", "session/end-seed"] := by
  rfl

end KnownTag

def dataIsObject : Lean.Json → Bool
  | .obj _ => true
  | _ => false

def optionIsNone {α : Type} : Option α → Bool
  | none => true
  | some _ => false

/-- The envelope metadata rule inherited from the current Harness discriminated union. -/
def metadataIsLegal (tag : KnownTag) (envelope : Envelope) : Bool :=
  if tag.isSurface then
    true
  else
    optionIsNone envelope.sourceEventSeqs && optionIsNone envelope.surfaceOp

/-- A parsed envelope known to be one of the pinned core tags. -/
structure KnownEnvelope where
  envelope : Envelope
  tag : KnownTag
  tag_result : KnownTag.fromString envelope.type = some tag
  data_is_object : dataIsObject envelope.data = true
  metadata_is_legal : metadataIsLegal tag envelope = true

namespace KnownEnvelope

def raw (known : KnownEnvelope) : Lean.Json := known.envelope.raw

theorem raw_eq (known : KnownEnvelope) : known.raw = known.envelope.raw := rfl

end KnownEnvelope

/-- Errors specific to the full tag-coverage boundary. -/
inductive ArchiveError where
  | envelope (index : Nat) (error : SessionArchive.ArchiveError)
  | knownDataNotObject (index : Nat) (tag : KnownTag)
  | knownMetadata (index : Nat) (tag : KnownTag)
  deriving BEq, DecidableEq, Repr

/-- A known event that the smaller semantic decoder accepted. -/
structure Supported where
  known : KnownEnvelope
  event : SessionRefinement.WireEvent
  decoded : SessionRefinement.decodeEvent known.envelope.raw = .ok event

/-- Every syntactically valid event is retained, with a distinction between known and unknown. -/
inductive ArchivedEvent where
  | supported (certificate : Supported)
  | knownOpaqueRequired (known : KnownEnvelope)
  | knownOpaqueIgnorable (known : KnownEnvelope)
  | extensionRequired (envelope : Envelope)
  | extensionIgnorable (envelope : Envelope)

namespace ArchivedEvent

def envelope : ArchivedEvent → Envelope
  | .supported certificate => certificate.known.envelope
  | .knownOpaqueRequired known => known.envelope
  | .knownOpaqueIgnorable known => known.envelope
  | .extensionRequired envelope => envelope
  | .extensionIgnorable envelope => envelope

def raw (event : ArchivedEvent) : Lean.Json := event.envelope.raw

def tag? : ArchivedEvent → Option KnownTag
  | .supported certificate => some certificate.known.tag
  | .knownOpaqueRequired known => some known.tag
  | .knownOpaqueIgnorable known => some known.tag
  | .extensionRequired _ | .extensionIgnorable _ => none

def isKnown : ArchivedEvent → Bool
  | .supported _ | .knownOpaqueRequired _ | .knownOpaqueIgnorable _ => true
  | .extensionRequired _ | .extensionIgnorable _ => false

def isOpaque : ArchivedEvent → Bool
  | .supported _ => false
  | .knownOpaqueRequired _ | .knownOpaqueIgnorable _ => true
  | .extensionRequired _ | .extensionIgnorable _ => true

def isRequired : ArchivedEvent → Bool
  | .supported _ => false
  | .knownOpaqueRequired _ | .extensionRequired _ => true
  | .knownOpaqueIgnorable _ | .extensionIgnorable _ => false

theorem raw_eq_envelope_raw (event : ArchivedEvent) :
    event.raw = event.envelope.raw := rfl

end ArchivedEvent

private def classifyKnown (known : KnownEnvelope) : ArchivedEvent :=
  match h : SessionRefinement.decodeEvent known.envelope.raw with
  | .ok event => .supported { known, event, decoded := h }
  | .error _ =>
      if known.envelope.isIgnorable then
        .knownOpaqueIgnorable known
      else
        .knownOpaqueRequired known

private def classifyExtension (envelope : Envelope) : ArchivedEvent :=
  if envelope.isIgnorable then
    .extensionIgnorable envelope
  else
    .extensionRequired envelope

private theorem classifyKnown_raw (known : KnownEnvelope) :
    (classifyKnown known).raw = known.envelope.raw := by
  unfold classifyKnown
  split
  · rfl
  · split <;> rfl

private theorem classifyExtension_raw (envelope : Envelope) :
    (classifyExtension envelope).raw = envelope.raw := by
  unfold classifyExtension
  split <;> rfl

private structure PreparedKnown (envelope : Envelope) where
  tag : KnownTag
  tag_result : KnownTag.fromString envelope.type = some tag
  data_is_object : dataIsObject envelope.data = true
  metadata_is_legal : metadataIsLegal tag envelope = true

private def prepareKnownAt (index : Nat) (envelope : Envelope) :
    Except ArchiveError (Option (PreparedKnown envelope)) :=
  match tagResult : KnownTag.fromString envelope.type with
  | none => .ok none
  | some tag =>
      if dataObject : dataIsObject envelope.data then
        if metadata : metadataIsLegal tag envelope then
          .ok (some {
            tag,
            tag_result := tagResult,
            data_is_object := dataObject,
            metadata_is_legal := metadata
          })
        else
          .error (.knownMetadata index tag)
      else
        .error (.knownDataNotObject index tag)

private def archiveEventAt (index : Nat) (raw : Lean.Json) :
    Except ArchiveError { event : ArchivedEvent // event.raw = raw } :=
  match envelopeResult : SessionArchive.decodeEnvelopeAtPath [.index index] raw with
  | .error error => .error (.envelope index error)
  | .ok envelope =>
      match preparedResult : prepareKnownAt index envelope with
      | .error error => .error error
      | .ok none =>
          let event := classifyExtension envelope
          .ok ⟨event, by
            have envelopeRaw :=
              SessionArchive.decodeEnvelopeAtPath_raw [.index index] raw envelope envelopeResult
            exact (classifyExtension_raw envelope).trans envelopeRaw⟩
      | .ok (some prepared) =>
          let known : KnownEnvelope := {
            envelope,
            tag := prepared.tag,
            tag_result := prepared.tag_result,
            data_is_object := prepared.data_is_object,
            metadata_is_legal := prepared.metadata_is_legal
          }
          let event := classifyKnown known
          .ok ⟨event, by
            have knownRaw := classifyKnown_raw known
            have envelopeRaw :=
              SessionArchive.decodeEnvelopeAtPath_raw [.index index] raw envelope envelopeResult
            exact knownRaw.trans envelopeRaw⟩

private structure ArchivedEvents (input : List Lean.Json) where
  events : List ArchivedEvent
  length_eq : events.length = input.length
  raw_eq : events.map ArchivedEvent.raw = input

private def archiveEventsAt : (index : Nat) → (input : List Lean.Json) →
    Except ArchiveError (ArchivedEvents input)
  | _, [] => .ok { events := [], length_eq := rfl, raw_eq := rfl }
  | index, raw :: rest =>
      match headResult : archiveEventAt index raw with
      | .error error => .error error
      | .ok head =>
          match tailResult : archiveEventsAt (index + 1) rest with
          | .error error => .error error
          | .ok tail =>
              .ok {
                events := head.1 :: tail.events
                length_eq := by simp [tail.length_eq]
                raw_eq := by simp [head.2, tail.raw_eq]
              }

/-- A full known-tag archive, preserving every input AST in order. -/
structure ArchivedLog (input : List Lean.Json) where
  events : List ArchivedEvent
  length_eq : events.length = input.length
  raw_eq : events.map ArchivedEvent.raw = input

namespace ArchivedLog

theorem length_exact {input : List Lean.Json} (archive : ArchivedLog input) :
    archive.events.length = input.length :=
  archive.length_eq

theorem raw_exact {input : List Lean.Json} (archive : ArchivedLog input) :
    archive.events.map ArchivedEvent.raw = input :=
  archive.raw_eq

def tags {input : List Lean.Json} (archive : ArchivedLog input) : List (Option KnownTag) :=
  archive.events.map ArchivedEvent.tag?

def knownCount {input : List Lean.Json} (archive : ArchivedLog input) : Nat :=
  archive.events.countP (fun event => event.isKnown)

end ArchivedLog

/-- Decode all envelopes and retain both semantic certificates and known opaque payloads. -/
def archive (input : List Lean.Json) : Except ArchiveError (ArchivedLog input) :=
  match _result : archiveEventsAt 0 input with
  | .error error => .error error
  | .ok events => .ok {
      events := events.events
      length_eq := events.length_eq
      raw_eq := events.raw_eq
    }

/-! ## Full-union fixtures -/

private def eventJson (tag : String) (seq : Nat) (data : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str tag),
    ("seq", .num seq),
    ("time", .num (Lean.JsonNumber.fromNat (100 + seq))),
    ("data", data)
  ]

private def surfaceEventJson (tag : String) (seq : Nat) (data : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str tag),
    ("seq", .num seq),
    ("time", .num (Lean.JsonNumber.fromNat (100 + seq))),
    ("data", data),
    ("surfaceOp", .str "append")
  ]

def allKnownEventJson : List Lean.Json :=
  [ eventJson "turn/start" 0 (Lean.Json.mkObj [("turn", .num 0)]),
    eventJson "turn/end" 1 (Lean.Json.mkObj [("turn", .num 0), ("reason", .str "completed")]),
    eventJson "step/start" 2 (Lean.Json.mkObj [("turn", .num 0), ("step", .num 0)]),
    eventJson "step/end" 3 (Lean.Json.mkObj [("turn", .num 0), ("step", .num 0)]),
    surfaceEventJson "user/message" 4 (Lean.Json.mkObj []),
    eventJson "assistant/chunk" 5 (Lean.Json.mkObj [("turn", .num 0), ("step", .num 0)]),
    surfaceEventJson "assistant/message" 6 (Lean.Json.mkObj [("turn", .num 0), ("step", .num 0)]),
    eventJson "tool/call" 7 (Lean.Json.mkObj [
      ("turn", .num 0), ("step", .num 0), ("callId", .str "call-0"),
      ("name", .str "echo"), ("arguments", .str "{}")]),
    surfaceEventJson "tool/result" 8 (Lean.Json.mkObj [("turn", .num 0), ("step", .num 0)]),
    eventJson "todo/write" 9 (Lean.Json.mkObj [("todos", .arr #[])]),
    eventJson "request/header" 10 (Lean.Json.mkObj [
      ("header", Lean.Json.mkObj []), ("reason", .str "initial")]),
    eventJson "request/context" 11 (Lean.Json.mkObj [
      ("provider", .str "fixture"), ("model", .str "fixture")]),
    eventJson "session/end-seed" 12 (Lean.Json.mkObj []) ]

def allKnownTagWires : List String :=
  match archive allKnownEventJson with
  | .error _ => []
  | .ok log => log.events.map (fun event =>
      match event.tag? with
      | some tag => tag.wire
      | none => "extension")

theorem all_known_tags_covered :
    allKnownTagWires = KnownTag.all.map KnownTag.wire := by
  rfl

theorem all_known_raw_preserved :
    (match archive allKnownEventJson with
    | .error _ => []
    | .ok log => log.events.map ArchivedEvent.raw) = allKnownEventJson := by
  rfl

def unsupportedReasoningSurfaceJson : Lean.Json :=
  surfaceEventJson "assistant/message" 0 (Lean.Json.mkObj [
    ("turn", .num 0),
    ("step", .num 0),
    ("message", Lean.Json.mkObj [
      ("id", .str "assistant-0"),
      ("role", .str "assistant"),
      ("source", Lean.Json.mkObj [
        ("kind", .str "model"), ("provider", .str "fixture"), ("model", .str "fixture")]),
      ("content", Lean.Json.arr #[Lean.Json.mkObj [
        ("type", .str "reasoning"), ("text", .str "opaque reasoning")]])]) ])

def unsupportedToolResultMetaJson : Lean.Json :=
  surfaceEventJson "tool/result" 0 (Lean.Json.mkObj [
    ("turn", .num 0),
    ("step", .num 0),
    ("message", Lean.Json.mkObj []),
    ("error", Lean.Json.mkObj [("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
    ("meta", Lean.Json.mkObj [("opaque", .str "tool-owned")])])

def requiredExtensionJson : Lean.Json :=
  SessionArchive.requiredExtensionJson

def ignorableExtensionJson : Lean.Json :=
  SessionArchive.ignorableExtensionJson

theorem reasoning_surface_is_known_opaque :
    (match archive [unsupportedReasoningSurfaceJson] with
    | .error _ => none
    | .ok log =>
        match log.events with
        | [event] => some (event.isOpaque, event.tag?)
        | _ => none) =
      some (true, some .assistantMessage) := by
  rfl

theorem tool_result_meta_is_known_opaque :
    (match archive [unsupportedToolResultMetaJson] with
    | .error _ => none
    | .ok log =>
        match log.events with
        | [event] => some (event.isOpaque, event.tag?)
        | _ => none) =
      some (true, some .toolResult) := by
  rfl

def illegalLogOnlyMetadataJson : Lean.Json :=
  surfaceEventJson "turn/start" 0 (Lean.Json.mkObj [("turn", .num 0)])

theorem reject_log_only_surface_metadata :
    archive [illegalLogOnlyMetadataJson] =
      .error (.knownMetadata 0 .turnStart) := by
  rfl

def knownNonObjectDataJson : Lean.Json :=
  eventJson "turn/start" 0 (.str "not-an-object")

theorem reject_known_nonobject_data :
    archive [knownNonObjectDataJson] =
      .error (.knownDataNotObject 0 .turnStart) := by
  rfl

theorem extensions_remain_opaque :
    (match archive [requiredExtensionJson, ignorableExtensionJson] with
    | .error _ => []
    | .ok log => log.events.map (fun event =>
        (event.isKnown, event.isOpaque, event.isRequired))) =
      [(false, true, true), (false, true, false)] := by
  rfl

end Cordis.SessionEventArchive
