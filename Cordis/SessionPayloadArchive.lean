import Cordis.SessionEventArchive

/-!
# Typed raw payloads for the current Harness event union

`SessionEventArchive` proves that every current core tag is recognized and that every event
envelope is retained exactly.  This module takes the next source-honest step: it inspects the
payload objects that the pinned Harness puts behind those tags, while keeping the source JSON as
the authority.  Message content blocks and stream chunks are classified by their wire `type`
tag, including unknown extension tags; assistant usage and tool-result failure/meta values stay
as exact JSON because their provider/tool-owned schemas are not local CORDIS schemas.

Malformed known payloads are not discarded.  They become a typed archive error attached to the
already-retained event, while extensions remain untouched.  Thus this is a payload-shape and
lossless-retention certificate, not a claim that every source message can be projected into the
smaller semantic `Session` representation.
-/

set_option autoImplicit false

namespace Cordis.SessionPayloadArchive

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev KnownTag := SessionEventArchive.KnownTag
abbrev KnownEnvelope := SessionEventArchive.KnownEnvelope
abbrev ArchivedEvent := SessionEventArchive.ArchivedEvent
abbrev ArchivedLog := SessionEventArchive.ArchivedLog

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

/-- Errors from the typed payload-shape pass. -/
inductive PayloadError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment)
  | malformed (path : List PathSegment) (message : String)
  deriving BEq, DecidableEq, Repr

private def requireField (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except PayloadError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField (fieldPath path name))

/-- The five pinned core content-block tags plus a lossless extension case. -/
inductive BlockTag where
  | text
  | reasoning
  | image
  | toolCall
  | toolResult
  | unknown (wire : String)
  deriving BEq, DecidableEq, Repr

namespace BlockTag

def fromString : String → BlockTag
  | "text" => .text
  | "reasoning" => .reasoning
  | "image" => .image
  | "tool-call" => .toolCall
  | "tool-result" => .toolResult
  | wire => .unknown wire

def wire : BlockTag → String
  | .text => "text"
  | .reasoning => "reasoning"
  | .image => "image"
  | .toolCall => "tool-call"
  | .toolResult => "tool-result"
  | .unknown wire => wire

end BlockTag

/-- The wire block tag, if the block is an object with a string `type` field. -/
def blockTag? : Lean.Json → Option BlockTag
  | .obj fields =>
      match fields.get? "type" with
      | some (.str wire) => some (BlockTag.fromString wire)
      | _ => none
  | _ => none

/-- One content block retained with both its source AST and its classified wire tag. -/
structure RawContentBlock where
  source : Lean.Json
  tag : BlockTag

namespace RawContentBlock

def raw (block : RawContentBlock) : Lean.Json := block.source

theorem raw_eq (block : RawContentBlock) : block.raw = block.source := rfl

end RawContentBlock

private structure DecodedBlock (input : Lean.Json) where
  block : RawContentBlock
  source_eq : block.source = input

private def decodeBlockAt (path : List PathSegment) (json : Lean.Json) :
    Except PayloadError (DecodedBlock json) :=
  match json with
  | .obj fields =>
      match fields.get? "type" with
      | none => .error (.missingField (fieldPath path "type"))
      | some (.str wire) =>
          let tag := BlockTag.fromString wire
          .ok {
            block := {
              source := Lean.Json.obj fields
              tag := tag
            }
            source_eq := rfl
          }
      | some value =>
          .error (.typeMismatch (fieldPath path "type") "string" (jsonKind value))
  | value => .error (.typeMismatch path "object" (jsonKind value))

private structure DecodedBlockList (input : List Lean.Json) where
  blocks : List RawContentBlock
  raw_eq : blocks.map RawContentBlock.raw = input

private def decodeBlockList : Nat → (input : List Lean.Json) →
    Except PayloadError (DecodedBlockList input)
  | _, [] => .ok { blocks := [], raw_eq := rfl }
  | index, head :: tail =>
      match headResult : decodeBlockAt (indexPath [] index) head with
      | .error error => .error error
      | .ok decoded =>
          match tailResult : decodeBlockList (index + 1) tail with
          | .error error => .error error
          | .ok suffix =>
              .ok {
                blocks := decoded.block :: suffix.blocks
                raw_eq := by simp [RawContentBlock.raw, decoded.source_eq, suffix.raw_eq]
              }

/-- An array-valued `content` field with exact element order and raw source retained. -/
structure RawContent where
  source : Lean.Json
  values : Array Lean.Json
  blocks : List RawContentBlock
  blocks_raw_eq : blocks.map RawContentBlock.raw = values.toList

namespace RawContent

def blockTags (content : RawContent) : List BlockTag := content.blocks.map RawContentBlock.tag

theorem blocks_raw_exact (content : RawContent) :
    content.blocks.map RawContentBlock.raw = content.values.toList :=
  content.blocks_raw_eq

end RawContent

private structure DecodedContent (input : Lean.Json) where
  content : RawContent
  source_eq : content.source = input

private def decodeContent (path : List PathSegment) (json : Lean.Json) :
    Except PayloadError (DecodedContent json) :=
  match json with
  | .arr values =>
      match result : decodeBlockList 0 values.toList with
      | .error error => .error error
      | .ok decoded =>
          .ok {
            content := {
              source := Lean.Json.arr values
              values := values
              blocks := decoded.blocks
              blocks_raw_eq := by simpa using decoded.raw_eq
            }
            source_eq := rfl
          }
  | value => .error (.typeMismatch path "array of content blocks" (jsonKind value))

/-- A JSON object retaining its exact field map. -/
structure RawObject where
  source : Lean.Json
  fields : Std.TreeMap.Raw String Lean.Json compare

namespace RawObject

def field (object : RawObject) (name : String) : Option Lean.Json := object.fields.get? name

end RawObject

private structure DecodedObject (input : Lean.Json) where
  object : RawObject
  source_eq : object.source = input

private def decodeObject (path : List PathSegment) (json : Lean.Json) :
    Except PayloadError (DecodedObject json) :=
  match json with
  | .obj fields => .ok {
      object := { source := Lean.Json.obj fields, fields := fields }
      source_eq := rfl
    }
  | value => .error (.typeMismatch path "object" (jsonKind value))

/-- A source message with lossless content-block classification. -/
structure RawMessage where
  object : RawObject
  content : RawContent
  content_field : object.field "content" = some content.source
  id : Option Lean.Json
  role : Option Lean.Json
  messageSource : Option Lean.Json

namespace RawMessage

def blockTags (message : RawMessage) : List BlockTag := message.content.blockTags

def source (message : RawMessage) : Lean.Json := message.object.source

theorem content_raw_exact (message : RawMessage) :
    message.content.blocks.map RawContentBlock.raw = message.content.values.toList :=
  message.content.blocks_raw_exact

end RawMessage

private def decodeRawMessage (path : List PathSegment) (json : Lean.Json) :
    Except PayloadError RawMessage :=
  match _objectResult : decodeObject path json with
  | .error error => .error error
  | .ok decodedObject =>
      let object := decodedObject.object
      match contentResult : object.field "content" with
      | none => .error (.missingField (fieldPath path "content"))
      | some contentJson =>
          match decodedResult : decodeContent (fieldPath path "content") contentJson with
          | .error error => .error error
          | .ok decodedContent =>
              let content := decodedContent.content
              .ok {
                object
                content
                content_field := by
                  exact contentResult.trans (congrArg some decodedContent.source_eq.symm)
                id := object.field "id"
                role := object.field "role"
                messageSource := object.field "source"
              }

/-- A raw stream chunk object; its complete payload remains in `object`. -/
structure RawChunk where
  object : RawObject
  type : String
  type_field : object.field "type" = some (.str type)

namespace RawChunk

def source (chunk : RawChunk) : Lean.Json := chunk.object.source

end RawChunk

private def decodeRawChunk (path : List PathSegment) (json : Lean.Json) :
    Except PayloadError RawChunk :=
  match _objectResult : decodeObject path json with
  | .error error => .error error
  | .ok decodedObject =>
      let object := decodedObject.object
      match typeResult : object.field "type" with
      | none => .error (.missingField (fieldPath path "type"))
      | some (.str type) => .ok { object, type, type_field := typeResult }
      | some value => .error (.typeMismatch (fieldPath path "type") "string" (jsonKind value))

/-- Typed raw shape information for one known event payload.

The optional fields are populated only where the pinned event union places them: `message` for
the three surface message events, `chunk` for `assistant/chunk`, `usage` for `assistant/message`,
and `error`/`meta` for `tool/result`.  They remain JSON rather than being projected into local
CORDIS values, so provider/tool-owned schemas and unknown extension fields are not lost. -/
structure PayloadView where
  tag : KnownTag
  object : RawObject
  message : Option RawMessage
  chunk : Option RawChunk
  usage : Option Lean.Json
  errorJson : Option Lean.Json
  metaJson : Option Lean.Json

namespace PayloadView

def blockTags (view : PayloadView) : Option (List BlockTag) := view.message.map RawMessage.blockTags

def contentBlockCount (view : PayloadView) : Option Nat := view.blockTags.map List.length

def data (view : PayloadView) : Lean.Json := view.object.source

end PayloadView

private def objectPayload (known : KnownEnvelope) :
    Except PayloadError (DecodedObject known.envelope.data) :=
  decodeObject [.field "data"] known.envelope.data

/-- Decode the current known-payload shapes while preserving all source fields. -/
def decodeKnown (known : KnownEnvelope) : Except PayloadError PayloadView := do
  let decodedObject ← objectPayload known
  let object := decodedObject.object
  match known.tag with
  | .userMessage =>
      let message ← decodeRawMessage [.field "data"] known.envelope.data
      .ok {
        tag := known.tag
        object
        message := some message
        chunk := none
        usage := none
        errorJson := none
        metaJson := none
      }
  | .assistantChunk =>
      let chunkJson ← requireField known.envelope.data [.field "data"] "chunk"
      let chunk ← decodeRawChunk [.field "data", .field "chunk"] chunkJson
      .ok {
        tag := known.tag
        object
        message := none
        chunk := some chunk
        usage := none
        errorJson := none
        metaJson := none
      }
  | .assistantMessage =>
      let messageJson ← requireField known.envelope.data [.field "data"] "message"
      let message ← decodeRawMessage [.field "data", .field "message"] messageJson
      .ok {
        tag := known.tag
        object
        message := some message
        chunk := none
        usage := object.field "usage"
        errorJson := none
        metaJson := none
      }
  | .toolResult =>
      let messageJson ← requireField known.envelope.data [.field "data"] "message"
      let message ← decodeRawMessage [.field "data", .field "message"] messageJson
      .ok {
        tag := known.tag
        object
        message := some message
        chunk := none
        usage := none
        errorJson := object.field "error"
        metaJson := object.field "meta"
      }
  | tag =>
      .ok {
        tag
        object
        message := none
        chunk := none
        usage := none
        errorJson := none
        metaJson := none
      }

/-- A known event whose payload shape was decoded, or retained with a precise shape error. -/
inductive EnrichedEvent where
  | typed (event : ArchivedEvent) (payload : PayloadView)
  | knownOpaque (event : ArchivedEvent) (error : PayloadError)
  | extension (event : ArchivedEvent)

namespace EnrichedEvent

def raw : EnrichedEvent → Lean.Json
  | .typed event _ => SessionEventArchive.ArchivedEvent.raw event
  | .knownOpaque event _ => SessionEventArchive.ArchivedEvent.raw event
  | .extension event => SessionEventArchive.ArchivedEvent.raw event

def isTyped : EnrichedEvent → Bool
  | .typed _ _ => true
  | .knownOpaque _ _ | .extension _ => false

def tag? : EnrichedEvent → Option KnownTag
  | .typed _ payload => some payload.tag
  | .knownOpaque event _ => SessionEventArchive.ArchivedEvent.tag? event
  | .extension _ => none

def blockTags : EnrichedEvent → Option (List BlockTag)
  | .typed _ payload => payload.blockTags
  | .knownOpaque _ _ | .extension _ => none

theorem raw_eq_event_raw (event : EnrichedEvent) : event.raw =
    match event with
    | .typed source _ => SessionEventArchive.ArchivedEvent.raw source
    | .knownOpaque source _ => SessionEventArchive.ArchivedEvent.raw source
    | .extension source => SessionEventArchive.ArchivedEvent.raw source := by
  cases event <;> rfl

end EnrichedEvent

private def enrichKnown (event : ArchivedEvent) (known : KnownEnvelope) : EnrichedEvent :=
  match decodeKnown known with
  | .ok payload => .typed event payload
  | .error error => .knownOpaque event error

private theorem enrichKnown_raw (event : ArchivedEvent) (known : KnownEnvelope) :
    (enrichKnown event known).raw = SessionEventArchive.ArchivedEvent.raw event := by
  unfold enrichKnown
  cases decodeKnown known <;> rfl

/-- Enrich a lossless tag archive without changing event order or source bytes. -/
def enrichEvent : ArchivedEvent → EnrichedEvent
  | event@(.supported certificate) => enrichKnown event certificate.known
  | event@(.knownOpaqueRequired known) => enrichKnown event known
  | event@(.knownOpaqueIgnorable known) => enrichKnown event known
  | event@(.extensionRequired _) => .extension event
  | event@(.extensionIgnorable _) => .extension event

theorem enrichEvent_raw (event : ArchivedEvent) :
    (enrichEvent event).raw = SessionEventArchive.ArchivedEvent.raw event := by
  cases event with
  | supported certificate => exact enrichKnown_raw _ certificate.known
  | knownOpaqueRequired known => exact enrichKnown_raw _ known
  | knownOpaqueIgnorable known => exact enrichKnown_raw _ known
  | extensionRequired envelope => rfl
  | extensionIgnorable envelope => rfl

/-- Event-by-event payload archive, retaining the original tag archive as its source certificate. -/
structure PayloadLog (input : List Lean.Json) where
  source : ArchivedLog input
  events : List EnrichedEvent
  length_eq : events.length = source.events.length
  raw_eq : events.map EnrichedEvent.raw = source.events.map SessionEventArchive.ArchivedEvent.raw

namespace PayloadLog

theorem length_exact {input : List Lean.Json} (log : PayloadLog input) :
    log.events.length = input.length := by
  rw [log.length_eq, log.source.length_exact]

theorem raw_exact {input : List Lean.Json} (log : PayloadLog input) :
    log.events.map EnrichedEvent.raw = input := by
  rw [log.raw_eq, log.source.raw_exact]

def typedCount {input : List Lean.Json} (log : PayloadLog input) : Nat :=
  log.events.countP EnrichedEvent.isTyped

end PayloadLog

def enrich {input : List Lean.Json} (archive : ArchivedLog input) : PayloadLog input := {
  source := archive
  events := archive.events.map enrichEvent
  length_eq := by simp
  raw_eq := by simp [enrichEvent_raw]
}

/-- Decode and enrich a raw Harness event list in one lossless pass. -/
def archivePayload (input : List Lean.Json) :
    Except SessionEventArchive.ArchiveError (PayloadLog input) :=
  match SessionEventArchive.archive input with
  | .error error => .error error
  | .ok archive => .ok (enrich archive)

/-! ## Executable source-shaped payload fixtures -/

private def eventJson (tag : String) (seq : Nat) (data : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str tag),
    ("seq", .num seq),
    ("time", .num (Lean.JsonNumber.fromNat (200 + seq))),
    ("data", data),
    ("surfaceOp", .str "append")]

def reasoningImagePayloadJson : Lean.Json :=
  eventJson "assistant/message" 0 (Lean.Json.mkObj [
    ("turn", .num 0),
    ("step", .num 0),
    ("message", Lean.Json.mkObj [
      ("id", .str "assistant-payload-0"),
      ("role", .str "assistant"),
      ("source", Lean.Json.mkObj [
        ("kind", .str "model"), ("provider", .str "fixture"), ("model", .str "fixture")]),
      ("content", Lean.Json.arr #[
        Lean.Json.mkObj [("type", .str "reasoning"), ("text", .str "hidden")],
        Lean.Json.mkObj [("type", .str "image"),
          ("attachment", Lean.Json.mkObj [("id", .str "image-0")])],
        Lean.Json.mkObj [("type", .str "text"), ("text", .str "visible")]])]),
    ("usage", Lean.Json.mkObj [
      ("inputTokens", .num 4), ("outputTokens", .num 3), ("reasoningTokens", .num 2)])])

def toolResultOpaquePayloadJson : Lean.Json :=
  eventJson "tool/result" 0 (Lean.Json.mkObj [
    ("turn", .num 0),
    ("step", .num 0),
    ("message", Lean.Json.mkObj [
      ("id", .str "tool-result-payload-0"),
      ("role", .str "user"),
      ("source", Lean.Json.mkObj [
        ("kind", .str "tool"), ("callId", .str "call-0")]),
      ("content", Lean.Json.arr #[Lean.Json.mkObj [
        ("type", .str "tool-result"),
        ("toolCallId", .str "call-0"),
        ("content", Lean.Json.arr #[Lean.Json.mkObj [
          ("type", .str "text"), ("text", .str "failure")]]),
        ("isError", .bool true)]])]),
    ("error", Lean.Json.mkObj [
      ("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
    ("meta", Lean.Json.mkObj [("owner", .str "tool")])])

def unknownBlockPayloadJson : Lean.Json :=
  eventJson "user/message" 0 (Lean.Json.mkObj [
    ("id", .str "user-payload-0"),
    ("role", .str "user"),
    ("source", Lean.Json.mkObj [("kind", .str "user")]),
    ("content", Lean.Json.arr #[Lean.Json.mkObj [
      ("type", .str "plugin-card"), ("payload", .str "opaque")]])])

def malformedMessagePayloadJson : Lean.Json :=
  eventJson "assistant/message" 0 (Lean.Json.mkObj [
    ("turn", .num 0),
    ("step", .num 0),
    ("message", Lean.Json.mkObj [
      ("id", .str "bad"), ("role", .str "assistant"),
      ("source", Lean.Json.mkObj []), ("content", .str "not-an-array")])])

def reasoningImageTyped : Bool :=
  match archivePayload [reasoningImagePayloadJson] with
  | .ok log =>
      match log.events with
      | [event] => event.isTyped && event.blockTags =
          some [.reasoning, .image, .text]
      | _ => false
  | .error _ => false

def toolResultOpaqueTyped : Bool :=
  match archivePayload [toolResultOpaquePayloadJson] with
  | .ok log =>
      match log.events with
      | [event] => event.isTyped && event.tag? = some .toolResult
      | _ => false
  | .error _ => false

def assistantUsageCaptured : Bool :=
  match archivePayload [reasoningImagePayloadJson] with
  | .ok log =>
      match log.events with
      | [.typed _ payload] => payload.usage.isSome
      | _ => false
  | .error _ => false

def toolResultErrorMetaCaptured : Bool :=
  match archivePayload [toolResultOpaquePayloadJson] with
  | .ok log =>
      match log.events with
      | [.typed _ payload] => payload.errorJson.isSome && payload.metaJson.isSome
      | _ => false
  | .error _ => false

def unknownBlockRetained : Bool :=
  match archivePayload [unknownBlockPayloadJson] with
  | .ok log =>
      match log.events with
      | [event] => event.blockTags = some [.unknown "plugin-card"]
      | _ => false
  | .error _ => false

def malformedPayloadIsRetained : Bool :=
  match archivePayload [malformedMessagePayloadJson] with
  | .ok log =>
      match log.events with
      | [event] => !EnrichedEvent.isTyped event &&
          EnrichedEvent.raw event == malformedMessagePayloadJson
      | _ => false
  | .error _ => false

end Cordis.SessionPayloadArchive
