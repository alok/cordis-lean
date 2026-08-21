import Cordis.RuntimeRefinement
import Cordis.SessionValidation
import Lean.Data.Json.Printer

/-!
# Stateful current-Harness session refinement

This module refines a source-shaped subset of DeepSeek Harness `SessionEvent` JSON at upstream
commit `99f6f02` into both local `Session` append witnesses and local intrinsic `Protocol` events.
The current upstream envelope is `{ type, seq, time, data, ignorable?, sourceEventSeqs?,
surfaceOp? }`; this decoder retains `seq` and `time`, rejects `ignorable`, and admits surface
 metadata for the supported append/replacement surface subset.

The translation synthesizes only values fixed by the accepted prefix and named normalizations:

* upstream steps begin at one; local protocol steps begin at zero, so `n + 1` maps to `n`;
* `turn/end` has no upstream `nextStep`; it is read from the validated local `.turn` state;
* provider string call ids receive the next fresh local numeric id and remain in a certified map;
* absent tool-result `isError` becomes `false`, matching the TypeScript optional Boolean default.

The supported event vocabulary is turn/step boundaries, restricted request headers, route context,
whole-list todo snapshots, empty session-seed markers, text/reasoning assistant chunks,
text-only user messages, assistant messages with text and complete tool-call blocks, tool calls,
and a restricted
tool result whose three call-id occurrences agree and whose nested result content is exactly one
text block. Only upstream `completed` and `max-tokens` turn-end reasons map without information
loss. Surface messages retain their upstream identity and source metadata in the refinement state
while their text and typed tool calls are projected into the smaller local `Session.Message`
vocabulary. Request-header wire witnesses retain the provider/model, optional system text, selected
tool schemas, and stop reason; the local `Session.RequestHeader` projection retains the fields it
represents. Route context, todo items, and the empty seed boundary are retained as typed log-only
payloads. Assistant chunks retain only text-delta blocks at index zero as log-only events.

Assistant reasoning blocks inside surface `assistant/message` records, assistant replay state,
tool-result error identity/meta, multimodal tool
results, unknown todo statuses, nonempty seed payloads, and all extension events are rejected.
Complete assistant tool calls are allocated into the same provider-to-local
binding state used by later `tool/call` and `tool/result` events. Their upstream payloads still
contain arbitrary JSON, provenance, replay data, or modalities absent from the local types. The
wire witness retains upstream `time`; the local session has no timestamp field, so no local
projection claim mentions it. This is a sound supported-subset refinement, not a
behavioral-equivalence claim or a general current/future session-log reader. JSON text parsing,
UTF-8, timestamps as wall-clock facts, persistence framing, and storage recovery remain outside.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev JsonKind := RuntimeRefinement.JsonKind

/-- Path-aware failures while decoding the supported current session-event subset. -/
inductive DecodeError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | invalidLength (path : List PathSegment) (expected actual : Nat)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | unsupportedField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Nat)
  deriving BEq, DecidableEq, Repr

/-- Turn-end reasons shared without loss by the upstream and local vocabularies. -/
inductive WireTurnEndReason where
  | completed
  | maxTokens
  deriving BEq, DecidableEq, Repr

namespace WireTurnEndReason

def toLocal : WireTurnEndReason → Session.TurnEndReason
  | .completed => .completed
  | .maxTokens => .maxTokens

end WireTurnEndReason

/-- The restricted request-header stop reason retained from the upstream envelope. -/
inductive WireRequestHeaderReason where
  | initial
  | resume
  | change
  deriving BEq, DecidableEq, Repr

/-- A tool schema whose JSON parameters are compressed into the local schema string field. -/
structure WireRequestToolSchema where
  name : String
  description : String
  parameters : String
  deriving DecidableEq, Repr

/-- The selected source-shaped request header fields admitted by this refinement. -/
structure WireRequestHeader where
  provider : String
  model : String
  system : Option String
  tools : List WireRequestToolSchema
  reason : WireRequestHeaderReason
  deriving DecidableEq, Repr

namespace WireRequestHeader

def toLocalTool (tool : WireRequestToolSchema) : Session.ToolSchema := {
  name := tool.name
  description := tool.description
  inputSchema := tool.parameters
}

def toLocal (header : WireRequestHeader) : Session.RequestHeader := {
  provider := header.provider
  model := header.model
  system := header.system
  toolSchemas := header.tools.map WireRequestHeader.toLocalTool
}

end WireRequestHeader

/-- A source-shaped todo status; the whole list is a log-only snapshot. -/
inductive WireTodoStatus where
  | pending
  | inProgress
  | completed
  deriving BEq, DecidableEq, Repr

structure WireTodoItem where
  content : String
  status : WireTodoStatus
  deriving DecidableEq, Repr

structure WireTodoWrite where
  todos : List WireTodoItem
  deriving DecidableEq, Repr

namespace WireTodoStatus

def toLocal : WireTodoStatus → Session.TodoStatus
  | .pending => .pending
  | .inProgress => .inProgress
  | .completed => .completed

end WireTodoStatus

namespace WireTodoWrite

def toLocalItem (item : WireTodoItem) : Session.TodoItem := {
  content := item.content
  status := item.status.toLocal
}

def toLocal (write : WireTodoWrite) : Session.TodoWritePayload := {
  todos := write.todos.map WireTodoWrite.toLocalItem
}

end WireTodoWrite

/-- Route metadata separate from the full request/header snapshot. -/
structure WireRequestContext where
  provider : String
  model : String
  contextWindow : Option SafeNat
  deriving DecidableEq, Repr

namespace WireRequestContext

def toLocal (context : WireRequestContext) : Session.RequestContext := {
  provider := context.provider
  model := context.model
  contextWindow := context.contextWindow.map (fun value => value.value)
}

end WireRequestContext

/-- A text `assistant/chunk` payload. Reasoning chunks use `WireReasoningChunk`. -/
structure WireAssistantChunk where
  turn : SafeNat
  step : SafeNat
  text : String
  deriving DecidableEq, Repr

/-- A reasoning `assistant/chunk` payload retained as a log-only event. -/
structure WireReasoningChunk where
  turn : SafeNat
  step : SafeNat
  text : String
  deriving DecidableEq, Repr

/-- Surface operations use the upstream object's `{ op, start, end }` shape for replacement. -/
inductive WireSurfaceOp where
  | append
  | replace (start endSeq : SafeNat)
  deriving DecidableEq, Repr

/-- Restricted, still source-shaped fields of one current upstream tool result. -/
structure WireToolResult where
  turn : SafeNat
  step : SafeNat
  messageId : String
  sourceCallId : String
  blockCallId : String
  content : String
  isError : Bool
  sourceEventSeqs : List SafeNat
  surfaceOp : WireSurfaceOp
  deriving DecidableEq, Repr

/-- One text block retained from an upstream surface message. -/
structure WireTextBlock where
  text : String
  deriving DecidableEq, Repr

/-- The admitted assistant block subset retains text and complete tool-call blocks. -/
inductive WireAssistantBlock where
  | text (text : String)
  | toolCall (providerId name arguments : String)
  deriving DecidableEq, Repr

/-- The source-shaped fields preserved for an admitted user message. -/
structure WireUserMessage where
  id : String
  content : List WireTextBlock
  deriving DecidableEq, Repr

/-- Optional token accounting retained on an admitted assistant message. -/
structure WireUsage where
  inputTokens : SafeNat
  outputTokens : SafeNat
  cacheReadTokens : Option SafeNat
  cacheWriteTokens : Option SafeNat
  reasoningTokens : Option SafeNat
  deriving DecidableEq, Repr

/-- The source-shaped fields preserved for an admitted assistant message. -/
structure WireAssistantMessage where
  id : String
  provider : String
  model : String
  content : List WireAssistantBlock
  usage : Option WireUsage
  deriving DecidableEq, Repr

/-- Surface messages retained separately from the smaller local session projection. -/
inductive WireSurfaceMessage where
  | user (message : WireUserMessage)
  | assistant (message : WireAssistantMessage)
  deriving DecidableEq, Repr

/-- A source surface message together with its optional upstream provenance references. -/
structure WireSurfaceAppend where
  message : WireSurfaceMessage
  sourceEventSeqs : Option (List SafeNat)
  surfaceOp : WireSurfaceOp
  deriving DecidableEq, Repr

/-- Supported payloads selected by the current upstream event `type`. -/
inductive WirePayload where
  | turnStart (turn : SafeNat)
  | turnEnd (turn : SafeNat) (reason : WireTurnEndReason)
  | stepStart (turn step : SafeNat)
  | stepEnd (turn step : SafeNat)
  | requestHeader (header : WireRequestHeader)
  | todoWrite (write : WireTodoWrite)
  | requestContext (context : WireRequestContext)
  | sessionEndSeed
  | assistantChunk (chunk : WireAssistantChunk)
  | assistantReasoningChunk (chunk : WireReasoningChunk)
  | userMessage (append : WireSurfaceAppend)
  | assistantMessage (turn step : SafeNat) (append : WireSurfaceAppend)
  | toolCall (turn step : SafeNat) (providerCallId name arguments : String)
  | toolResult (result : WireToolResult)
  deriving DecidableEq, Repr

/-- Current upstream outer event envelope with retained sequence and timestamp. -/
structure WireEvent where
  seq : SafeNat
  time : SafeNat
  payload : WirePayload
  deriving DecidableEq, Repr

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

private def requireField (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def rejectPresent (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError Unit :=
  if (field? json name).isSome then
    .error (.unsupportedField path name)
  else
    .ok ()

private def decodeString (path : List PathSegment) : Lean.Json → Except DecodeError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeBool (path : List PathSegment) : Lean.Json → Except DecodeError Bool
  | .bool value => .ok value
  | json => .error (.typeMismatch path "boolean" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json → Except DecodeError SafeNat
  | .num ⟨Int.ofNat value, 0⟩ =>
      if safe : value ≤ RuntimeRefinement.maxSafeInteger then
        .ok { value, safe }
      else
        .error (.unsafeInteger path value)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError String := do
  decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError SafeNat := do
  decodeSafeNat (fieldPath path name) (← requireField json path name)

private def decodeOptionalNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option SafeNat) :=
  match field? json name with
  | none => .ok none
  | some value => some <$> decodeSafeNat (fieldPath path name) value

private def decodeOptionalString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option String) :=
  match field? json name with
  | none => .ok none
  | some .null => .ok none
  | some value => some <$> decodeString (fieldPath path name) value

private def decodeOptionalBool (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option Bool) :=
  match field? json name with
  | none => .ok none
  | some value => return some (← decodeBool (fieldPath path name) value)

private def decodeSafeNatList (path : List PathSegment) : Lean.Json →
    Except DecodeError (List SafeNat)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List SafeNat)
        | _, [] => .ok []
        | index, value :: rest => do
            let decoded ← decodeSafeNat (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok (decoded :: suffix)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeSingleton (path : List PathSegment) : Lean.Json →
    Except DecodeError Lean.Json
  | .arr values =>
      match values.toList with
      | [value] => .ok value
      | values => .error (.invalidLength path 1 values.length)
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def expectTag (path : List PathSegment) (expected actual : String) :
    Except DecodeError Unit :=
  if actual = expected then
    .ok ()
  else
    .error (.unsupportedTag path actual)

private def rejectSurfaceMetadata (json : Lean.Json) (path : List PathSegment) :
    Except DecodeError Unit := do
  rejectPresent json path "surfaceOp"
  rejectPresent json path "sourceEventSeqs"

private def decodeTurnEndReason (path : List PathSegment) : Lean.Json →
    Except DecodeError WireTurnEndReason
  | json@(.obj _) => do
      let kind ← decodeRequiredString json path "kind"
      match kind with
      | "completed" => .ok .completed
      | "max-tokens" => .ok .maxTokens
      | kind => .error (.unsupportedTag (fieldPath path "kind") kind)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeTextBlock (path : List PathSegment) : Lean.Json → Except DecodeError String
  | json@(.obj _) => do
      expectTag (fieldPath path "type") "text" (← decodeRequiredString json path "type")
      decodeRequiredString json path "text"
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeTextBlocks (path : List PathSegment) : Lean.Json →
    Except DecodeError (List WireTextBlock)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List WireTextBlock)
        | _, [] => .ok []
        | index, value :: rest => do
            let text ← decodeTextBlock (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok ({ text } :: suffix)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeAssistantBlock (path : List PathSegment) : Lean.Json →
    Except DecodeError WireAssistantBlock
  | json@(.obj _) => do
      let kind ← decodeRequiredString json path "type"
      match kind with
      | "text" => .text <$> decodeRequiredString json path "text"
      | "tool-call" =>
          .toolCall <$> decodeRequiredString json path "id"
            <*> decodeRequiredString json path "name"
            <*> decodeRequiredString json path "arguments"
      | tag => .error (.unsupportedTag (fieldPath path "type") tag)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeAssistantBlocks (path : List PathSegment) : Lean.Json →
    Except DecodeError (List WireAssistantBlock)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List WireAssistantBlock)
        | _, [] => .ok []
        | index, value :: rest => do
            let decoded ← decodeAssistantBlock (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok (decoded :: suffix)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeWireUsage (path : List PathSegment) : Lean.Json →
    Except DecodeError WireUsage
  | json@(.obj _) => do
      .ok {
        inputTokens := ← decodeRequiredNat json path "inputTokens"
        outputTokens := ← decodeRequiredNat json path "outputTokens"
        cacheReadTokens := ← decodeOptionalNat json path "cacheReadTokens"
        cacheWriteTokens := ← decodeOptionalNat json path "cacheWriteTokens"
        reasoningTokens := ← decodeOptionalNat json path "reasoningTokens"
      }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeOptionalWireUsage (json : Lean.Json) (path : List PathSegment) :
    Except DecodeError (Option WireUsage) :=
  match field? json "usage" with
  | none | some .null => .ok none
  | some value => some <$> decodeWireUsage (fieldPath path "usage") value

private def decodeUserMessage (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError WireUserMessage := do
  let id ← decodeRequiredString json path "id"
  expectTag (fieldPath path "role") "user"
    (← decodeRequiredString json path "role")
  let source ← requireField json path "source"
  let sourcePath := fieldPath path "source"
  match source with
  | .obj _ =>
      expectTag (fieldPath sourcePath "kind") "user"
        (← decodeRequiredString source sourcePath "kind")
  | value => .error (.typeMismatch sourcePath "object" (jsonKind value))
  let content ← decodeTextBlocks (fieldPath path "content")
    (← requireField json path "content")
  .ok { id, content }

private def decodeAssistantMessage (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError WireAssistantMessage := do
  let id ← decodeRequiredString json path "id"
  expectTag (fieldPath path "role") "assistant"
    (← decodeRequiredString json path "role")
  let source ← requireField json path "source"
  let sourcePath := fieldPath path "source"
  let provider ← match source with
    | .obj _ => do
        expectTag (fieldPath sourcePath "kind") "model"
          (← decodeRequiredString source sourcePath "kind")
        rejectPresent source sourcePath "replayState"
        decodeRequiredString source sourcePath "provider"
    | value => .error (.typeMismatch sourcePath "object" (jsonKind value))
  let model ← decodeRequiredString source sourcePath "model"
  let content ← decodeAssistantBlocks (fieldPath path "content")
    (← requireField json path "content")
  let usage ← decodeOptionalWireUsage json path
  .ok { id, provider, model, content, usage }

private structure DecodedSurfaceMetadata where
  surfaceOp : WireSurfaceOp
  sourceEventSeqs : Option (List SafeNat)

private def decodeSurfaceMetadata (event : Lean.Json) (path : List PathSegment) :
    Except DecodeError DecodedSurfaceMetadata := do
  let surfaceOpJson ← requireField event path "surfaceOp"
  let surfaceOpPath := fieldPath path "surfaceOp"
  let surfaceOp ← match surfaceOpJson with
    | .str "append" => .ok .append
    | .obj _ => do
        let op ← decodeRequiredString surfaceOpJson surfaceOpPath "op"
        expectTag (fieldPath surfaceOpPath "op") "replace" op
        let start ← decodeRequiredNat surfaceOpJson surfaceOpPath "start"
        let endSeq ← decodeRequiredNat surfaceOpJson surfaceOpPath "end"
        .ok (.replace start endSeq)
    | json => .error (.typeMismatch surfaceOpPath "string or object" (jsonKind json))
  let sourceEventSeqs ← match field? event "sourceEventSeqs" with
    | none => .ok none
    | some value => some <$> decodeSafeNatList (fieldPath path "sourceEventSeqs") value
  .ok { surfaceOp, sourceEventSeqs }

private def decodeUserMessageData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError WireSurfaceAppend := do
  let message ← decodeUserMessage dataPath data
  let metadata ← decodeSurfaceMetadata event eventPath
  .ok {
    message := .user message
    sourceEventSeqs := metadata.sourceEventSeqs
    surfaceOp := metadata.surfaceOp
  }

private def decodeAssistantMessageData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError (SafeNat × SafeNat × WireSurfaceAppend) := do
  let turn ← decodeRequiredNat data dataPath "turn"
  let step ← decodeRequiredNat data dataPath "step"
  let messageJson ← requireField data dataPath "message"
  let messagePath := fieldPath dataPath "message"
  let message ← match messageJson with
    | .obj _ => decodeAssistantMessage messagePath messageJson
    | value => .error (.typeMismatch messagePath "object" (jsonKind value))
  let usage ← decodeOptionalWireUsage data dataPath
  let message := { message with usage }
  let metadata ← decodeSurfaceMetadata event eventPath
  .ok (turn, step, {
    message := .assistant message
    sourceEventSeqs := metadata.sourceEventSeqs
    surfaceOp := metadata.surfaceOp
  })

private def decodeWireRequestToolSchema (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError WireRequestToolSchema :=
  match json with
  | .obj _ => do
      let name ← decodeRequiredString json path "name"
      let description ← decodeRequiredString json path "description"
      let parameters ← requireField json path "parameters"
      match parameters with
      | .obj _ => .ok {
          name, description, parameters := Lean.Json.compress parameters
        }
      | value => .error (.typeMismatch (fieldPath path "parameters") "object" (jsonKind value))
  | value => .error (.typeMismatch path "object" (jsonKind value))

private def decodeWireRequestToolSchemas (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError (List WireRequestToolSchema) :=
  match json with
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List WireRequestToolSchema)
        | _, [] => .ok []
        | index, value :: rest => do
            let tool ← decodeWireRequestToolSchema (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok (tool :: suffix)
      loop 0 values.toList
  | value => .error (.typeMismatch path "array" (jsonKind value))

private def decodeWireRequestHeaderReason (path : List PathSegment) : Lean.Json →
    Except DecodeError WireRequestHeaderReason
  | .str "initial" => .ok .initial
  | .str "resume" => .ok .resume
  | .str "change" => .ok .change
  | .str reason => .error (.unsupportedTag path reason)
  | value => .error (.typeMismatch path "string" (jsonKind value))

private def decodeWireTodoStatus (path : List PathSegment) : Lean.Json →
    Except DecodeError WireTodoStatus
  | .str "pending" => .ok .pending
  | .str "in_progress" => .ok .inProgress
  | .str "completed" => .ok .completed
  | .str status => .error (.unsupportedTag path status)
  | value => .error (.typeMismatch path "string" (jsonKind value))

private def decodeWireTodoItem (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError WireTodoItem :=
  match json with
  | .obj _ => do
      let content ← decodeRequiredString json path "content"
      let status ← decodeWireTodoStatus (fieldPath path "status")
        (← requireField json path "status")
      .ok { content, status }
  | value => .error (.typeMismatch path "object" (jsonKind value))

private def decodeWireTodoItems (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError (List WireTodoItem) :=
  match json with
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List WireTodoItem)
        | _, [] => .ok []
        | index, value :: rest => do
            let item ← decodeWireTodoItem (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok (item :: suffix)
      loop 0 values.toList
  | value => .error (.typeMismatch path "array" (jsonKind value))

private def decodeWireTodoWriteData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) : Except DecodeError WireTodoWrite := do
  rejectSurfaceMetadata event eventPath
  let todos ← decodeWireTodoItems (fieldPath dataPath "todos")
    (← requireField data dataPath "todos")
  .ok { todos }

private def decodeWireRequestContextData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError WireRequestContext := do
  rejectSurfaceMetadata event eventPath
  let provider ← decodeRequiredString data dataPath "provider"
  let model ← decodeRequiredString data dataPath "model"
  let contextWindow ← decodeOptionalNat data dataPath "contextWindow"
  .ok { provider, model, contextWindow }

private def decodeWireSessionEndSeedData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError Unit :=
  match data with
  | .obj fields =>
      match fields.toList with
      | [] => do
          rejectSurfaceMetadata event eventPath
          .ok ()
      | (name, _) :: _ => do
          rejectSurfaceMetadata event eventPath
          .error (.unsupportedField dataPath name)
  | value => .error (.typeMismatch dataPath "object" (jsonKind value))

private def decodeWireRequestHeaderData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError WireRequestHeader := do
  rejectSurfaceMetadata event eventPath
  let headerJson ← requireField data dataPath "header"
  let headerPath := fieldPath dataPath "header"
  let header ← match headerJson with
    | .obj _ => .ok headerJson
    | value => .error (.typeMismatch headerPath "object" (jsonKind value))
  rejectPresent header headerPath "adapterDefaults"
  let configJson ← requireField header headerPath "config"
  let configPath := fieldPath headerPath "config"
  let config ← match configJson with
    | .obj _ => .ok configJson
    | value => .error (.typeMismatch configPath "object" (jsonKind value))
  rejectPresent config configPath "temperature"
  rejectPresent config configPath "maxTokens"
  rejectPresent config configPath "reasoningEffort"
  rejectPresent config configPath "stop"
  let provider ← decodeRequiredString config configPath "provider"
  let model ← decodeRequiredString config configPath "model"
  let system ← decodeOptionalString header headerPath "system"
  let tools ← match field? header "tools" with
    | none => .ok []
    | some value => decodeWireRequestToolSchemas (fieldPath headerPath "tools") value
  let reason ← decodeWireRequestHeaderReason (fieldPath dataPath "reason")
    (← requireField data dataPath "reason")
  .ok { provider, model, system, tools, reason }

private def decodeWireAssistantChunkData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError WireAssistantChunk := do
  rejectSurfaceMetadata event eventPath
  let turn ← decodeRequiredNat data dataPath "turn"
  let step ← decodeRequiredNat data dataPath "step"
  let chunkJson ← requireField data dataPath "chunk"
  let chunkPath := fieldPath dataPath "chunk"
  let chunk ← match chunkJson with
    | .obj _ => .ok chunkJson
    | value => .error (.typeMismatch chunkPath "object" (jsonKind value))
  expectTag (fieldPath chunkPath "type") "text-delta"
    (← decodeRequiredString chunk chunkPath "type")
  let index ← decodeRequiredNat chunk chunkPath "index"
  if index.value = 0 then
    .ok { turn, step, text := ← decodeRequiredString chunk chunkPath "text" }
  else
    .error (.unsupportedTag (fieldPath chunkPath "index") (toString index.value))

private def decodeWireReasoningChunkData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) :
    Except DecodeError WireReasoningChunk := do
  rejectSurfaceMetadata event eventPath
  let turn ← decodeRequiredNat data dataPath "turn"
  let step ← decodeRequiredNat data dataPath "step"
  let chunkJson ← requireField data dataPath "chunk"
  let chunkPath := fieldPath dataPath "chunk"
  let chunk ← match chunkJson with
    | .obj _ => .ok chunkJson
    | value => .error (.typeMismatch chunkPath "object" (jsonKind value))
  expectTag (fieldPath chunkPath "type") "reasoning-delta"
    (← decodeRequiredString chunk chunkPath "type")
  let index ← decodeRequiredNat chunk chunkPath "index"
  if index.value = 0 then
    .ok { turn, step, text := ← decodeRequiredString chunk chunkPath "text" }
  else
    .error (.unsupportedTag (fieldPath chunkPath "index") (toString index.value))

private structure DecodedToolResultBlock where
  callId : String
  content : String
  isError : Bool

private def decodeToolResultBlock (path : List PathSegment) : Lean.Json →
    Except DecodeError DecodedToolResultBlock
  | json@(.obj _) => do
      expectTag (fieldPath path "type") "tool-result"
        (← decodeRequiredString json path "type")
      let callId ← decodeRequiredString json path "toolCallId"
      let contentJson ← decodeSingleton (fieldPath path "content")
        (← requireField json path "content")
      let content ← decodeTextBlock (indexPath (fieldPath path "content") 0) contentJson
      let isError ← decodeOptionalBool json path "isError"
      .ok { callId, content, isError := isError.getD false }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeToolResultData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) : Except DecodeError WireToolResult := do
  rejectPresent data dataPath "error"
  rejectPresent data dataPath "meta"
  let turn ← decodeRequiredNat data dataPath "turn"
  let step ← decodeRequiredNat data dataPath "step"
  let message ← requireField data dataPath "message"
  let messagePath := fieldPath dataPath "message"
  match message with
  | .obj _ =>
      let messageId ← decodeRequiredString message messagePath "id"
      expectTag (fieldPath messagePath "role") "user"
        (← decodeRequiredString message messagePath "role")
      let source ← requireField message messagePath "source"
      let sourcePath := fieldPath messagePath "source"
      let sourceCallId ← match source with
        | .obj _ => do
            expectTag (fieldPath sourcePath "kind") "tool"
              (← decodeRequiredString source sourcePath "kind")
            decodeRequiredString source sourcePath "callId"
        | json => .error (.typeMismatch sourcePath "object" (jsonKind json))
      let blockJson ← decodeSingleton (fieldPath messagePath "content")
        (← requireField message messagePath "content")
      let block ← decodeToolResultBlock
        (indexPath (fieldPath messagePath "content") 0) blockJson
      let metadata ← decodeSurfaceMetadata event eventPath
      let sources ← match metadata.sourceEventSeqs with
        | some sources => .ok sources
        | none => .error (.missingField eventPath "sourceEventSeqs")
      .ok {
        turn, step, messageId, sourceCallId
        blockCallId := block.callId
        content := block.content
        isError := block.isError
        sourceEventSeqs := sources
        surfaceOp := metadata.surfaceOp
      }
  | json => .error (.typeMismatch messagePath "object" (jsonKind json))

private def decodePayload (event : Lean.Json) (path : List PathSegment)
    (tag : String) (data : Lean.Json) : Except DecodeError WirePayload :=
  match data with
  | .obj _ =>
      let dataPath := fieldPath path "data"
      match tag with
      | "turn/start" => do
          rejectSurfaceMetadata event path
          return .turnStart (← decodeRequiredNat data dataPath "turn")
      | "turn/end" => do
          rejectSurfaceMetadata event path
          let turn ← decodeRequiredNat data dataPath "turn"
          let reason ← decodeTurnEndReason (fieldPath dataPath "reason")
            (← requireField data dataPath "reason")
          return .turnEnd turn reason
      | "step/start" => do
          rejectSurfaceMetadata event path
          return .stepStart
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
      | "step/end" => do
          rejectSurfaceMetadata event path
          return .stepEnd
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
      | "request/header" =>
          .requestHeader <$> decodeWireRequestHeaderData event path data dataPath
      | "todo/write" =>
          .todoWrite <$> decodeWireTodoWriteData event path data dataPath
      | "request/context" =>
          .requestContext <$> decodeWireRequestContextData event path data dataPath
      | "session/end-seed" => do
          let _ ← decodeWireSessionEndSeedData event path data dataPath
          return .sessionEndSeed
      | "assistant/chunk" =>
          match field? data "chunk" with
          | some (.obj fields) =>
              match fields.get? "type" with
              | some (.str "reasoning-delta") =>
                  .assistantReasoningChunk <$>
                    decodeWireReasoningChunkData event path data dataPath
              | _ => .assistantChunk <$> decodeWireAssistantChunkData event path data dataPath
          | _ => .assistantChunk <$> decodeWireAssistantChunkData event path data dataPath
      | "user/message" =>
          .userMessage <$> decodeUserMessageData event path data dataPath
      | "assistant/message" => do
          let (turn, step, append) ← decodeAssistantMessageData event path data dataPath
          return .assistantMessage turn step append
      | "tool/call" => do
          rejectSurfaceMetadata event path
          return .toolCall
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
            (← decodeRequiredString data dataPath "callId")
            (← decodeRequiredString data dataPath "name")
            (← decodeRequiredString data dataPath "arguments")
      | "tool/result" =>
          .toolResult <$> decodeToolResultData event path data dataPath
      | tag => .error (.unsupportedTag (fieldPath path "type") tag)
  | json => .error (.typeMismatch (fieldPath path "data") "object" (jsonKind json))

private def decodeEventAt (path : List PathSegment) : Lean.Json → Except DecodeError WireEvent
  | event@(.obj _) => do
      rejectPresent event path "ignorable"
      let tag ← decodeRequiredString event path "type"
      let seq ← decodeRequiredNat event path "seq"
      let time ← decodeRequiredNat event path "time"
      let data ← requireField event path "data"
      let payload ← decodePayload event path tag data
      .ok { seq, time, payload }
  | json => .error (.typeMismatch path "object" (jsonKind json))

/-- Decode one current upstream session-event JSON AST in the supported subset. -/
def decodeEvent (json : Lean.Json) : Except DecodeError WireEvent :=
  decodeEventAt [] json

private def decodeEventsAt : Nat → List Lean.Json → Except DecodeError (List WireEvent)
  | _, [] => .ok []
  | index, json :: rest => do
      let event ← decodeEventAt [.index index] json
      let events ← decodeEventsAt (index + 1) rest
      .ok (event :: events)

/-- Decode a current upstream JSON-AST event list with element-aware paths. -/
def decodeEvents (json : List Lean.Json) : Except DecodeError (List WireEvent) :=
  decodeEventsAt 0 json

/-! ## Prefix-derived call identity and state -/

/-- One current provider string id paired with its deterministic local numeric id. -/
structure CallBinding where
  providerId : String
  localId : CallId
  deriving DecidableEq, Repr

/-- Call-id assignment state with freshness facts exposed to later refinements. -/
structure BindingState where
  nextLocalId : Nat
  bindings : List CallBinding
  providerNodup : (bindings.map CallBinding.providerId).Nodup
  localNodup : (bindings.map CallBinding.localId).Nodup
  localBelowNext : ∀ binding ∈ bindings, binding.localId.value < nextLocalId

namespace BindingState

def empty : BindingState where
  nextLocalId := 0
  bindings := []
  providerNodup := by simp
  localNodup := by simp
  localBelowNext := by simp

def clear (state : BindingState) : BindingState where
  nextLocalId := state.nextLocalId
  bindings := []
  providerNodup := by simp
  localNodup := by simp
  localBelowNext := by simp

def findProvider (providerId : String) : List CallBinding → Option CallBinding
  | [] => none
  | binding :: rest =>
      if binding.providerId = providerId then some binding else findProvider providerId rest

end BindingState

/-- Refiner state advanced only by jointly successful Session and Protocol validation. -/
structure State where
  session : Session.Session Session.noExtensions
  protocol : SessionState
  calls : BindingState
  wireSurface : List WireSurfaceAppend

namespace State

/-- Current Harness turn numbering starts at one; local step normalization starts at zero. -/
def initial : State where
  session := Session.Session.empty Session.noExtensions
  protocol := .ready 1
  calls := .empty
  wireSurface := []

end State

/-- Stateful failures distinguish translation, session, and protocol rejection. -/
inductive RefinementError where
  | zeroStep
  | surfaceKindMismatch
  | duplicateProviderCall (providerId : String)
  | unknownProviderCall (providerId : String)
  | mismatchedToolResultIds (sourceId blockId : String)
  | cannotDeriveTurnEndStep (state : RuntimeState)
  | session (error : Session.ValidationError)
  | protocol (error : Cordis.ValidationError)
  deriving DecidableEq, Repr

private def normalizeStep (step : SafeNat) : Except RefinementError Nat :=
  match step.value with
  | 0 => .error .zeroStep
  | localStepValue + 1 => .ok localStepValue

private structure Allocation (before : BindingState) (providerId : String) where
  binding : CallBinding
  localId : CallId
  after : BindingState

private def allocate (before : BindingState) (providerId : String) :
    Except RefinementError (Allocation before providerId) :=
  if freshProvider : providerId ∉ before.bindings.map CallBinding.providerId then
    let localId : CallId := { value := before.nextLocalId }
    have freshLocal : localId ∉ before.bindings.map CallBinding.localId := by
      intro member
      rcases List.mem_map.mp member with ⟨binding, bindingMember, bindingEq⟩
      have below := before.localBelowNext binding bindingMember
      have equalValue := congrArg CallId.value bindingEq
      exact (Nat.ne_of_lt below) equalValue
    let binding : CallBinding := { providerId, localId }
    .ok {
      binding
      localId
      after := {
        nextLocalId := before.nextLocalId + 1
        bindings := binding :: before.bindings
        providerNodup := List.nodup_cons.mpr ⟨freshProvider, before.providerNodup⟩
        localNodup := List.nodup_cons.mpr ⟨freshLocal, before.localNodup⟩
        localBelowNext := by
          intro current member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact Nat.lt_succ_self before.nextLocalId
          · exact Nat.lt_succ_of_lt (before.localBelowNext current member)
      }
    }
  else
    .error (.duplicateProviderCall providerId)

private structure ToolAllocation where
  providerId : String
  localId : CallId
  name : String
  arguments : String

private def allocateAssistantCalls (before : BindingState) :
    List (String × String × String) →
      Except RefinementError (List ToolAllocation × BindingState)
  | [] => .ok ([], before)
  | (providerId, name, arguments) :: rest => do
      let allocated ← allocate before providerId
      let ⟨suffix, after⟩ ← allocateAssistantCalls allocated.after rest
      .ok ({ providerId, localId := allocated.localId, name, arguments } :: suffix, after)

private def assistantBlockTriples : List WireAssistantBlock → List (String × String × String)
  | [] => []
  | .text _ :: rest => assistantBlockTriples rest
  | .toolCall providerId name arguments :: rest =>
      (providerId, name, arguments) :: assistantBlockTriples rest

private def assistantBlockText : List WireAssistantBlock → String
  | [] => ""
  | .text text :: rest => text ++ assistantBlockText rest
  | .toolCall _ _ _ :: rest => assistantBlockText rest

private def toolAllocationsToSession : List ToolAllocation → List Session.ToolCall
  | [] => []
  | allocation :: rest =>
      { id := allocation.localId, name := allocation.name, arguments := allocation.arguments } ::
        toolAllocationsToSession rest

private def resolveCall (before : BindingState) (providerId : String) :
    Except RefinementError (CallBinding × BindingState) :=
  match BindingState.findProvider providerId before.bindings with
  | some binding => .ok (binding, before)
  | none => do
      let allocated ← allocate before providerId
      .ok (allocated.binding, allocated.after)

/-! ## Joint local candidates and proof-producing refinement -/

/-- Exact local event, protocol projection, and next call map proposed for one wire event. -/
structure Candidate (before : State) (wire : WireEvent) where
  localEvent : Session.LoggedEvent Session.noExtensions
  runtime : Option RuntimeEvent
  calls : BindingState
  wireAppend : Option WireSurfaceAppend
  seq_eq : localEvent.seq = wire.seq.value
  projection_eq : Session.LoggedEvent.protocolEvent? localEvent = runtime

private def logOnlyEvent (seq : Nat) (kind : Session.Kind Session.noExtensions .logOnly)
    (payload : kind.Payload) : Session.LoggedEvent Session.noExtensions where
  visibility := .logOnly
  seq
  kind
  payload
  intent := .token

private def toolResultEvent (seq : Nat) (payload : Session.ToolResultPayload)
    (intent : Session.SurfaceIntent) : Session.LoggedEvent Session.noExtensions where
  visibility := .surface
  seq
  kind := .toolResult
  payload
  intent := intent

private def userMessageEvent (seq : Nat) (content : String)
    (intent : Session.SurfaceIntent) : Session.LoggedEvent Session.noExtensions where
  visibility := .surface
  seq
  kind := .userMessage
  payload := { content }
  intent := intent

private def assistantMessageEvent (seq turn step : Nat) (content : String)
    (rawToolCalls : List Session.ToolCall) (intent : Session.SurfaceIntent) :
    Session.LoggedEvent Session.noExtensions where
  visibility := .surface
  seq
  kind := .assistantMessage
  payload := { turn, step, content, rawToolCalls }
  intent := intent

private def concatText : List WireTextBlock → String
  | [] => ""
  | block :: rest => block.text ++ concatText rest

private def sourceSeqsToNat : Option (List SafeNat) → List Nat
  | none => []
  | some values => values.map RuntimeRefinement.SafeNat.value

private def surfaceIntent (op : WireSurfaceOp) (sources : List Nat) : Session.SurfaceIntent :=
  match op with
  | .append => .append sources
  | .replace start endSeq => .replace start.value endSeq.value sources

private def userLocalContent (message : WireUserMessage) : String :=
  concatText message.content

private def assistantLocalContent (message : WireAssistantMessage) : String :=
  assistantBlockText message.content

private def expectUserMessage : WireSurfaceMessage → Except RefinementError WireUserMessage
  | .user message => .ok message
  | .assistant _ => .error .surfaceKindMismatch

private def expectAssistantMessage : WireSurfaceMessage →
    Except RefinementError WireAssistantMessage
  | .user _ => .error .surfaceKindMismatch
  | .assistant message => .ok message

private def candidate (before : State) (wire : WireEvent) :
    Except RefinementError (Candidate before wire) :=
  match wire.payload with
  | .turnStart turn =>
      let localEvent := logOnlyEvent wire.seq.value .turnStart { turn := turn.value }
      .ok {
        localEvent
        runtime := some (.turnStart turn.value)
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .turnEnd turn reason =>
      match before.protocol with
      | .turn _ nextStep =>
          let localEvent := logOnlyEvent wire.seq.value .turnEnd {
            turn := turn.value, nextStep, reason := reason.toLocal
          }
          .ok {
            localEvent
            runtime := some (.turnEnd turn.value nextStep)
            calls := before.calls.clear
            wireAppend := none
            seq_eq := rfl
            projection_eq := rfl
          }
      | protocol => .error (.cannotDeriveTurnEndStep (eraseState protocol))
  | .stepStart turn step => do
      let localStep ← normalizeStep step
      let localEvent := logOnlyEvent wire.seq.value .stepStart {
        turn := turn.value, step := localStep
      }
      .ok {
        localEvent
        runtime := some (.stepStart turn.value localStep)
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .stepEnd turn step => do
      let localStep ← normalizeStep step
      let localEvent := logOnlyEvent wire.seq.value .stepEnd {
        turn := turn.value, step := localStep
      }
      .ok {
        localEvent
        runtime := some (.stepEnd turn.value localStep)
        calls := before.calls.clear
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .requestHeader header =>
      let localEvent := logOnlyEvent wire.seq.value .requestHeader header.toLocal
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .todoWrite write =>
      let localEvent := logOnlyEvent wire.seq.value .todoWrite write.toLocal
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .requestContext context =>
      let localEvent := logOnlyEvent wire.seq.value .requestContext context.toLocal
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .sessionEndSeed =>
      let localEvent := logOnlyEvent wire.seq.value .sessionEndSeed {}
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .assistantChunk chunk => do
      let localStep ← normalizeStep chunk.step
      let localEvent := logOnlyEvent wire.seq.value .assistantChunk {
        turn := chunk.turn.value, step := localStep, delta := chunk.text
      }
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .assistantReasoningChunk chunk => do
      let localStep ← normalizeStep chunk.step
      let localEvent := logOnlyEvent wire.seq.value .assistantReasoning {
        turn := chunk.turn.value, step := localStep, delta := chunk.text
      }
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .toolCall turn step providerId name arguments => do
      let localStep ← normalizeStep step
      let ⟨binding, calls⟩ ← resolveCall before.calls providerId
      let localEvent := logOnlyEvent wire.seq.value .toolCall {
        turn := turn.value
        step := localStep
        call := { id := binding.localId, name, arguments }
      }
      .ok {
        localEvent
        runtime := some (.toolCall turn.value localStep binding.localId)
        calls
        wireAppend := none
        seq_eq := rfl
        projection_eq := rfl
      }
  | .userMessage append => do
      let message ← expectUserMessage append.message
      let sources := sourceSeqsToNat append.sourceEventSeqs
      let localEvent := userMessageEvent wire.seq.value
        (userLocalContent message) (surfaceIntent append.surfaceOp sources)
      .ok {
        localEvent
        runtime := none
        calls := before.calls
        wireAppend := some append
        seq_eq := rfl
        projection_eq := rfl
      }
  | .assistantMessage turn step append => do
      let localStep ← normalizeStep step
      let message ← expectAssistantMessage append.message
      let allocations ← allocateAssistantCalls before.calls
        (assistantBlockTriples message.content)
      let localEvent := assistantMessageEvent wire.seq.value turn.value localStep
        (assistantLocalContent message)
        (toolAllocationsToSession allocations.1)
        (surfaceIntent append.surfaceOp (sourceSeqsToNat append.sourceEventSeqs))
      .ok {
        localEvent
        runtime := none
        calls := allocations.2
        wireAppend := some append
        seq_eq := rfl
        projection_eq := rfl
      }
  | .toolResult result => do
      if _same : result.sourceCallId = result.blockCallId then
        let binding ← match
            BindingState.findProvider result.sourceCallId before.calls.bindings with
          | some binding => .ok binding
          | none => .error (.unknownProviderCall result.sourceCallId)
        let localStep ← normalizeStep result.step
        let sources := result.sourceEventSeqs.map (·.value)
        let localEvent := toolResultEvent wire.seq.value {
          turn := result.turn.value
          step := localStep
          callId := binding.localId
          content := result.content
          isError := result.isError
        } (surfaceIntent result.surfaceOp sources)
        .ok {
          localEvent
          runtime := some (.toolResult result.turn.value localStep binding.localId)
          calls := before.calls
          wireAppend := none
          seq_eq := rfl
          projection_eq := rfl
        }
      else
        .error (.mismatchedToolResultIds result.sourceCallId result.blockCallId)

/-- One wire event admitted by both local validators with exact structural projection. -/
inductive ProtocolDelta (before : SessionState) : Option RuntimeEvent → Type where
  | none : ProtocolDelta before none
  | some {runtime : RuntimeEvent}
      (validated : Cordis.ValidatedEvent before runtime) :
      ProtocolDelta before (some runtime)

namespace ProtocolDelta

def finish {before : SessionState} {runtime : Option RuntimeEvent}
    (delta : ProtocolDelta before runtime) : SessionState :=
  match delta with
  | .none => before
  | .some validated => validated.finish

def prependTrace
    {before finish : SessionState} {runtime : Option RuntimeEvent}
    (delta : ProtocolDelta before runtime)
    (tail : Cordis.Trace (ProtocolDelta.finish delta) finish) : Cordis.Trace before finish :=
  match delta with
  | .none => tail
  | .some validated => .cons validated.event tail

theorem prependTrace_erase
    {before finish : SessionState} {runtime : Option RuntimeEvent}
    (delta : ProtocolDelta before runtime)
    (tail : Cordis.Trace (ProtocolDelta.finish delta) finish) :
    (prependTrace delta tail).erase = runtime.toList ++ tail.erase := by
  cases delta with
  | none => rfl
  | some validated =>
      cases validated with
      | mk finish event erase_eq =>
          change event.erase :: tail.erase = _
          rw [erase_eq]
          simp

end ProtocolDelta

structure RefinedEvent (before : State) (wire : WireEvent) where
  candidate : Candidate before wire
  append : Session.ValidatedAppend before.session candidate.localEvent
  protocol : ProtocolDelta before.protocol candidate.runtime

namespace RefinedEvent

def after {before : State} {wire : WireEvent} (event : RefinedEvent before wire) : State where
  session := event.append.apply
  protocol := ProtocolDelta.finish event.protocol
  calls := event.candidate.calls
  wireSurface := before.wireSurface ++ event.candidate.wireAppend.toList

theorem after_protocol {before : State} {wire : WireEvent}
    (event : RefinedEvent before wire) :
    event.after.protocol = ProtocolDelta.finish event.protocol :=
  rfl

def tailAtFinish
    {before : State} {wire : WireEvent} {finish : SessionState}
    (event : RefinedEvent before wire)
    (tail : Cordis.Trace event.after.protocol finish) :
    Cordis.Trace (ProtocolDelta.finish event.protocol) finish :=
  by
    simpa [after_protocol] using tail

@[simp] theorem tailAtFinish_erase
    {before : State} {wire : WireEvent} {finish : SessionState}
    (event : RefinedEvent before wire)
    (tail : Cordis.Trace event.after.protocol finish) :
    (tailAtFinish event tail).erase = tail.erase := by
  simp [tailAtFinish, after_protocol]

/-- The appended local event projects to the exact raw protocol event that was validated. -/
theorem projection_exact {before : State} {wire : WireEvent}
    (event : RefinedEvent before wire) :
    Session.LoggedEvent.protocolEvent? event.candidate.localEvent =
      event.candidate.runtime :=
  event.candidate.projection_eq

/-- Physical local sequence identity is preserved exactly from the upstream envelope. -/
theorem seq_exact {before : State} {wire : WireEvent} (event : RefinedEvent before wire) :
    event.candidate.localEvent.seq = wire.seq.value :=
  event.candidate.seq_eq

/-- One accepted event extends the physical local log by exactly its translated event. -/
theorem events_eq {before : State} {wire : WireEvent} (event : RefinedEvent before wire) :
    event.after.session.events = before.session.events ++ [event.candidate.localEvent] :=
  event.append.apply_events

/-- One accepted append extends the local structural projection by its exact raw event. -/
theorem protocolProjection_eq {before : State} {wire : WireEvent}
    (event : RefinedEvent before wire) :
    Session.protocolProjection event.after.session.events =
      Session.protocolProjection before.session.events ++ event.candidate.runtime.toList := by
  rw [event.events_eq]
  simp only [Session.protocolProjection, List.filterMap_append]
  have singleton :
      List.filterMap Session.LoggedEvent.protocolEvent? [event.candidate.localEvent] =
        event.candidate.runtime.toList := by
    simp only [List.filterMap]
    rw [event.projection_exact]
    rfl
  rw [singleton]

end RefinedEvent

private def validateProtocol (before : SessionState) (runtime : Option RuntimeEvent) :
    Except RefinementError (ProtocolDelta before runtime) :=
  match runtime with
  | none => .ok .none
  | some raw =>
      match Cordis.validateEvent before raw with
      | .ok validated => .ok (.some validated)
      | .error error => .error (.protocol error)

/-- Translate and jointly validate one source-shaped wire event. -/
def refineEvent (before : State) (wire : WireEvent) :
    Except RefinementError (RefinedEvent before wire) := do
  let translated ← candidate before wire
  let append ← match Session.validateAppend before.session translated.localEvent with
    | .ok validated => .ok validated
    | .error error => .error (.session error)
  let protocol ← validateProtocol before.protocol translated.runtime
  .ok { candidate := translated, append, protocol }

/-- A sequential certificate chaining every jointly validated event. -/
inductive ValidatedSequence : State → List WireEvent → State → Type where
  | nil (state : State) : ValidatedSequence state [] state
  | cons {seed : State} {event : WireEvent} {rest : List WireEvent} {final : State}
      (head : RefinedEvent seed event)
      (tail : ValidatedSequence head.after rest final) :
      ValidatedSequence seed (event :: rest) final

namespace ValidatedSequence

/-- The intrinsic protocol trace obtained by composing each per-event witness. -/
def protocolTrace {seed final : State} {events : List WireEvent} :
    ValidatedSequence seed events final → Cordis.Trace seed.protocol final.protocol
  | .nil _ => .nil
  | .cons head tail =>
      by
        simpa [RefinedEvent.after] using
          (ProtocolDelta.prependTrace head.protocol
            (RefinedEvent.tailAtFinish head tail.protocolTrace))

/-- Runtime protocol erasure is exactly the per-event projection sequence. -/
def runtimeEvents {seed final : State} {events : List WireEvent} :
    ValidatedSequence seed events final → List RuntimeEvent
  | .nil _ => []
  | .cons head tail => head.candidate.runtime.toList ++ tail.runtimeEvents

theorem protocolTrace_erase {seed final : State} {events : List WireEvent}
    (sequence : ValidatedSequence seed events final) :
    sequence.protocolTrace.erase = sequence.runtimeEvents := by
  induction sequence with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simpa [protocolTrace, runtimeEvents, RefinedEvent.after] using
        (show (ProtocolDelta.prependTrace head.protocol
            (RefinedEvent.tailAtFinish head tail.protocolTrace)).erase =
            head.candidate.runtime.toList ++ tail.runtimeEvents by
          rw [ProtocolDelta.prependTrace_erase, RefinedEvent.tailAtFinish_erase,
            inductionHypothesis])

/-- The final local session projection is the seed projection followed by every refined event. -/
theorem sessionProjection_eq {seed final : State} {events : List WireEvent}
    (sequence : ValidatedSequence seed events final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection seed.session.events ++ sequence.runtimeEvents := by
  induction sequence with
  | nil => simp [runtimeEvents]
  | cons head tail inductionHypothesis =>
      rw [inductionHypothesis, head.protocolProjection_eq]
      simp [runtimeEvents, List.append_assoc]

end ValidatedSequence

/-- Validate a decoded wire sequence from left to right. -/
def validateSequence : (seed : State) → (events : List WireEvent) →
    Except RefinementError (Σ final, ValidatedSequence seed events final)
  | seed, [] => .ok ⟨seed, .nil seed⟩
  | seed, event :: rest => do
      let head ← refineEvent seed event
      let ⟨final, tail⟩ ← validateSequence head.after rest
      .ok ⟨final, .cons head tail⟩

/-- JSON input, exact decoded wire events, and their sequential joint certificate. -/
structure ValidatedJsonLog (input : List Lean.Json) where
  events : List WireEvent
  decode_eq : decodeEvents input = .ok events
  final : State
  sequence : ValidatedSequence State.initial events final

namespace ValidatedJsonLog

/-- The complete local protocol projection is exactly the intrinsic trace erasure. -/
theorem projection_exact {input : List Lean.Json} (validated : ValidatedJsonLog input) :
    Session.protocolProjection validated.final.session.events =
      validated.sequence.protocolTrace.erase := by
  rw [validated.sequence.sessionProjection_eq]
  simp [State.initial, Session.Session.empty, Session.protocolProjection]
  exact validated.sequence.protocolTrace_erase.symm

end ValidatedJsonLog

/-- Decode and jointly validate a finite supported current-Harness event prefix. -/
def validateJsonLog (input : List Lean.Json) :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) :=
  match decoded : decodeEvents input with
  | .error error => .error (.inl error)
  | .ok events =>
      match validateSequence State.initial events with
      | .error error => .error (.inr error)
      | .ok ⟨final, sequence⟩ => .ok { events, decode_eq := decoded, final, sequence }

/-! ## Executable current-shape example and rejection witnesses -/

def exampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 100),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 1), ("time", .num 101),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/call"), ("seq", .num 2), ("time", .num 102),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1), ("callId", .str "provider-call"),
      ("name", .str "lookup"), ("arguments", .str "{\"q\":\"lean\"}")
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/result"), ("seq", .num 3), ("time", .num 103),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("message", Lean.Json.mkObj [
        ("source", Lean.Json.mkObj [
          ("kind", .str "tool"), ("callId", .str "provider-call")
        ]),
        ("content", .arr #[Lean.Json.mkObj [
          ("type", .str "tool-result"), ("toolCallId", .str "provider-call"),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "text"), ("text", .str "result")
          ]]),
          ("isError", .bool false)
        ]]),
        ("role", .str "user"), ("id", .str "message-1")
      ])
    ]),
    ("sourceEventSeqs", .arr #[.num 2]), ("surfaceOp", .str "append")
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 4), ("time", .num 104),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 5), ("time", .num 105),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

/-! ## Text-message surface example -/

def messageExampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 200),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "user/message"), ("seq", .num 1), ("time", .num 201),
    ("data", Lean.Json.mkObj [
      ("id", .str "user-1"), ("role", .str "user"),
      ("source", Lean.Json.mkObj [("kind", .str "user")]),
      ("content", .arr #[Lean.Json.mkObj [
        ("type", .str "text"), ("text", .str "hello")
      ]])
    ]),
    ("surfaceOp", .str "append"), ("sourceEventSeqs", .arr #[])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 2), ("time", .num 202),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "assistant/message"), ("seq", .num 3), ("time", .num 203),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("message", Lean.Json.mkObj [
        ("id", .str "assistant-1"), ("role", .str "assistant"),
        ("source", Lean.Json.mkObj [
          ("kind", .str "model"), ("provider", .str "deepseek"),
          ("model", .str "deepseek-reasoner")
        ]),
        ("content", .arr #[Lean.Json.mkObj [
          ("type", .str "text"), ("text", .str "hi")
        ]])
      ]),
      ("usage", Lean.Json.mkObj [
        ("inputTokens", .num 4), ("outputTokens", .num 1)
      ])
    ]),
    ("surfaceOp", .str "append"), ("sourceEventSeqs", .arr #[.num 1])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 4), ("time", .num 204),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 5), ("time", .num 205),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

/-! ## Assistant tool-call surface example -/

def toolMessageExampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 300),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "user/message"), ("seq", .num 1), ("time", .num 301),
    ("data", Lean.Json.mkObj [
      ("id", .str "user-1"), ("role", .str "user"),
      ("source", Lean.Json.mkObj [("kind", .str "user")]),
      ("content", .arr #[Lean.Json.mkObj [
        ("type", .str "text"), ("text", .str "look up lean")
      ]])
    ]),
    ("surfaceOp", .str "append"), ("sourceEventSeqs", .arr #[])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 2), ("time", .num 302),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "assistant/message"), ("seq", .num 3), ("time", .num 303),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("message", Lean.Json.mkObj [
        ("id", .str "assistant-1"), ("role", .str "assistant"),
        ("source", Lean.Json.mkObj [
          ("kind", .str "model"), ("provider", .str "deepseek"),
          ("model", .str "deepseek-reasoner")
        ]),
        ("content", .arr #[
          Lean.Json.mkObj [("type", .str "text"), ("text", .str "I will look it up." )],
          Lean.Json.mkObj [
            ("type", .str "tool-call"), ("id", .str "provider-call"),
            ("name", .str "lookup"), ("arguments", .str "{\"q\":\"lean\"}")
          ]
        ])
      ])
    ]),
    ("surfaceOp", .str "append"), ("sourceEventSeqs", .arr #[.num 1])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/call"), ("seq", .num 4), ("time", .num 304),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1), ("callId", .str "provider-call"),
      ("name", .str "lookup"), ("arguments", .str "{\"q\":\"lean\"}")
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/result"), ("seq", .num 5), ("time", .num 305),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("message", Lean.Json.mkObj [
        ("source", Lean.Json.mkObj [
          ("kind", .str "tool"), ("callId", .str "provider-call")
        ]),
        ("content", .arr #[Lean.Json.mkObj [
          ("type", .str "tool-result"), ("toolCallId", .str "provider-call"),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "text"), ("text", .str "result")
          ]]),
          ("isError", .bool false)
        ]]),
        ("role", .str "user"), ("id", .str "message-1")
      ])
    ]),
    ("sourceEventSeqs", .arr #[.num 4]), ("surfaceOp", .str "append")
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 6), ("time", .num 306),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 7), ("time", .num 307),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1),
      ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

/-! ## Compaction-style replacement surface example -/

def replacementMessageExampleJson : List Lean.Json :=
  toolMessageExampleJson ++ [
    Lean.Json.mkObj [
      ("type", .str "assistant/message"), ("seq", .num 8), ("time", .num 308),
      ("data", Lean.Json.mkObj [
        ("turn", .num 1), ("step", .num 1),
        ("message", Lean.Json.mkObj [
          ("id", .str "assistant-summary"), ("role", .str "assistant"),
          ("source", Lean.Json.mkObj [
            ("kind", .str "model"), ("provider", .str "deepseek"),
            ("model", .str "deepseek-reasoner")
          ]),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "text"), ("text", .str "I summarized the lookup.")
          ]])
        ])
      ]),
      ("surfaceOp", Lean.Json.mkObj [
        ("op", .str "replace"), ("start", .num 3), ("end", .num 5)
      ]),
      ("sourceEventSeqs", .arr #[.num 3, .num 5])
    ]
  ]

def malformedReplacementMessageExampleJson : List Lean.Json :=
  toolMessageExampleJson ++ [
    Lean.Json.mkObj [
      ("type", .str "assistant/message"), ("seq", .num 8), ("time", .num 308),
      ("data", Lean.Json.mkObj [
        ("turn", .num 1), ("step", .num 1),
        ("message", Lean.Json.mkObj [
          ("id", .str "assistant-summary"), ("role", .str "assistant"),
          ("source", Lean.Json.mkObj [
            ("kind", .str "model"), ("provider", .str "deepseek"),
            ("model", .str "deepseek-reasoner")
          ]),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "text"), ("text", .str "I summarized the lookup.")
          ]])
        ])
      ]),
      ("surfaceOp", Lean.Json.mkObj [
        ("op", .str "replace"), ("start", .num 3), ("end", .num 5)
      ]),
      ("sourceEventSeqs", .arr #[.num 3])
    ]
  ]

/-! ## Request-header and text-chunk log-only example -/

def headerChunkParametersJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "object"),
  ("properties", Lean.Json.mkObj [("query", Lean.Json.mkObj [("type", .str "string")])])
]

def headerChunkExpectedHeader : Session.RequestHeader := {
  provider := "deepseek"
  model := "deepseek-reasoner"
  system := some "Answer briefly."
  toolSchemas := [{
    name := "lookup"
    description := "Look up a key"
    inputSchema := Lean.Json.compress headerChunkParametersJson
  }]
}

def headerChunkExampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "request/header"), ("seq", .num 0), ("time", .num 400),
    ("data", Lean.Json.mkObj [
      ("header", Lean.Json.mkObj [
        ("config", Lean.Json.mkObj [
          ("provider", .str "deepseek"), ("model", .str "deepseek-reasoner")
        ]),
        ("system", .str "Answer briefly."),
        ("tools", .arr #[Lean.Json.mkObj [
          ("name", .str "lookup"), ("description", .str "Look up a key"),
          ("parameters", headerChunkParametersJson)
        ]])
      ]),
      ("reason", .str "initial")
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 1), ("time", .num 401),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 2), ("time", .num 402),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "assistant/chunk"), ("seq", .num 3), ("time", .num 403),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("chunk", Lean.Json.mkObj [
        ("type", .str "text-delta"), ("index", .num 0), ("text", .str "hello")
      ])
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 4), ("time", .num 404),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 5), ("time", .num 405),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

/-! ## Todo/context/seed log-only example -/

def metadataExampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "request/context"), ("seq", .num 0), ("time", .num 500),
    ("data", Lean.Json.mkObj [
      ("provider", .str "deepseek"), ("model", .str "deepseek-reasoner"),
      ("contextWindow", .num 131072)
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "todo/write"), ("seq", .num 1), ("time", .num 501),
    ("data", Lean.Json.mkObj [
      ("todos", .arr #[
        Lean.Json.mkObj [("content", .str "formalize context"), ("status", .str "completed")],
        Lean.Json.mkObj [("content", .str "audit session seed"), ("status", .str "in_progress")]
      ])
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "session/end-seed"), ("seq", .num 2), ("time", .num 502),
    ("data", Lean.Json.mkObj [])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 3), ("time", .num 503),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 4), ("time", .num 504),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "assistant/chunk"), ("seq", .num 5), ("time", .num 505),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("chunk", Lean.Json.mkObj [
        ("type", .str "text-delta"), ("index", .num 0), ("text", .str "seeded")
      ])
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 6), ("time", .num 506),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 7), ("time", .num 507),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

def malformedTodoStatusExampleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "todo/write"), ("seq", .num 0), ("time", .num 0),
  ("data", Lean.Json.mkObj [
    ("todos", .arr #[
      Lean.Json.mkObj [("content", .str "blocked task"), ("status", .str "blocked")]
    ])
  ])
]

def malformedSessionEndSeedExampleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "session/end-seed"), ("seq", .num 0), ("time", .num 0),
  ("data", Lean.Json.mkObj [("unexpected", .bool true)])
]

def malformedAssistantChunkExampleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "assistant/chunk"), ("seq", .num 0), ("time", .num 0),
  ("data", Lean.Json.mkObj [
    ("turn", .num 1), ("step", .num 1),
    ("chunk", Lean.Json.mkObj [
      ("type", .str "reasoning-delta"), ("index", .num 0), ("text", .str "hidden")
    ])
  ])
]

def malformedAssistantChunkIndexExampleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "assistant/chunk"), ("seq", .num 0), ("time", .num 0),
  ("data", Lean.Json.mkObj [
    ("turn", .num 1), ("step", .num 1),
    ("chunk", Lean.Json.mkObj [
      ("type", .str "text-delta"), ("index", .num 1), ("text", .str "hello")
    ])
  ])
]

def malformedRequestHeaderExampleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "request/header"), ("seq", .num 0), ("time", .num 0),
  ("data", Lean.Json.mkObj [
    ("header", Lean.Json.mkObj [
      ("config", Lean.Json.mkObj [
        ("provider", .str "deepseek"), ("model", .str "deepseek-reasoner"),
        ("temperature", .num 0)
      ])
    ]),
    ("reason", .str "initial")
  ])
]

private def wireSurfaceIds : List WireSurfaceAppend → List String
  | [] => []
  | append :: rest =>
      let id := match append.message with
        | .user message => message.id
        | .assistant message => message.id
      id :: wireSurfaceIds rest

private def wireSurfaceProviders : List WireSurfaceAppend → List String
  | [] => []
  | append :: rest =>
      let provider := match append.message with
        | .user _ => ""
        | .assistant message => message.provider
      provider :: wireSurfaceProviders rest

structure SurfaceValidationSummary where
  protocol : SessionState
  messages : List Session.Message
  runtimeEvents : List RuntimeEvent
  surfaceIds : List String
  surfaceProviders : List String
  deriving DecidableEq

def surfaceValidationSummary {input : List Lean.Json} :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) →
      Option SurfaceValidationSummary
  | .error _ => none
  | .ok validated => some {
      protocol := validated.final.protocol
      messages := validated.final.session.messages
      runtimeEvents := validated.sequence.runtimeEvents
      surfaceIds := wireSurfaceIds validated.final.wireSurface
      surfaceProviders := wireSurfaceProviders validated.final.wireSurface
    }

/-- Proof-erased observation used only to state executable example outcomes compactly. -/
structure ValidationSummary where
  protocol : SessionState
  nextSeq : Nat
  messages : List Session.Message
  runtimeEvents : List RuntimeEvent
  deriving DecidableEq

/-- Observe a successful certificate without replacing the proof-producing return type. -/
def validationSummary {input : List Lean.Json} :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) → Option ValidationSummary
  | .error _ => none
  | .ok validated => some {
      protocol := validated.final.protocol
      nextSeq := validated.final.session.nextSeq
      messages := validated.final.session.messages
      runtimeEvents := validated.sequence.runtimeEvents
    }

def latestHeaderSummary {input : List Lean.Json} :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) →
      Option (Option Session.RequestHeader)
  | .error _ => none
  | .ok validated => some validated.final.session.latestHeader

/-- Full supported JSON prefix reaches a closed local turn and one tool-result surface node. -/
theorem validate_example :
    validationSummary (validateJsonLog exampleJson) = some {
      protocol := .ready 2
      nextSeq := 6
      messages := [.toolResult { value := 0 } "result" false]
      runtimeEvents := [
        .turnStart 1,
        .stepStart 1 0,
        .toolCall 1 0 { value := 0 },
        .toolResult 1 0 { value := 0 },
        .stepEnd 1 0,
        .turnEnd 1 1
      ]
    } := by
  rfl

/-- Local `nextStep = 1` at turn end is derived from the preceding certified step transition. -/
theorem example_turnEndStep_isDerived :
    (validationSummary (validateJsonLog exampleJson)).map
      (fun summary => summary.runtimeEvents.getLast?) = some (some (.turnEnd 1 1)) := by
  rfl

/-- Text surface events append locally while their upstream IDs and provider
    are retained in state. -/
theorem validate_message_example :
    surfaceValidationSummary (validateJsonLog messageExampleJson) = some {
        protocol := .ready 2
        messages := [.user "hello", .assistant "hi" []]
        runtimeEvents := [
          .turnStart 1,
          .stepStart 1 0,
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
        surfaceIds := ["user-1", "assistant-1"]
        surfaceProviders := ["", "deepseek"]
      } := by
  rfl

/-- Assistant tool-call blocks allocate a local ID reused by later call/result events. -/
theorem validate_tool_message_example :
    surfaceValidationSummary (validateJsonLog toolMessageExampleJson) = some {
        protocol := .ready 2
        messages := [
          .user "look up lean",
          .assistant "I will look it up." [{
            id := { value := 0 }, name := "lookup", arguments := "{\"q\":\"lean\"}"
          }],
          .toolResult { value := 0 } "result" false
        ]
        runtimeEvents := [
          .turnStart 1,
          .stepStart 1 0,
          .toolCall 1 0 { value := 0 },
          .toolResult 1 0 { value := 0 },
          .stepEnd 1 0,
          .turnEnd 1 1
      ]
        surfaceIds := ["user-1", "assistant-1"]
        surfaceProviders := ["", "deepseek"]
      } := by
  decide

/-- A source-shaped replacement shadows the assistant/tool-result surface interval exactly. -/
theorem validate_replacement_message_example :
    surfaceValidationSummary (validateJsonLog replacementMessageExampleJson) = some {
        protocol := .ready 2
        messages := [.user "look up lean", .assistant "I summarized the lookup." []]
        runtimeEvents := [
          .turnStart 1,
          .stepStart 1 0,
          .toolCall 1 0 { value := 0 },
          .toolResult 1 0 { value := 0 },
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
        surfaceIds := ["user-1", "assistant-1", "assistant-summary"]
        surfaceProviders := ["", "deepseek", "deepseek"]
      } := by
  decide

/-- A restricted request header and text delta are retained as log-only events while the
    structural protocol still reaches the same closed turn. -/
theorem validate_header_chunk_example :
    validationSummary (validateJsonLog headerChunkExampleJson) = some {
      protocol := .ready 2
      nextSeq := 6
      messages := []
      runtimeEvents := [
        .turnStart 1,
        .stepStart 1 0,
        .stepEnd 1 0,
        .turnEnd 1 1
      ]
    } := by
  decide

theorem validate_header_chunk_latestHeader :
    latestHeaderSummary (validateJsonLog headerChunkExampleJson) =
      some (some headerChunkExpectedHeader) := by
  rfl

/-- Todo, route-context, and seed-boundary events remain log-only while a later turn still
    validates through the same stateful protocol/refinement fold. -/
theorem validate_metadata_example :
    validationSummary (validateJsonLog metadataExampleJson) = some {
      protocol := .ready 2
      nextSeq := 8
      messages := []
      runtimeEvents := [
        .turnStart 1,
        .stepStart 1 0,
        .stepEnd 1 0,
        .turnEnd 1 1
      ]
    } := by
  rfl

/-- Todo statuses are a closed source union; unknown status strings fail at their indexed path. -/
theorem reject_todo_unknownStatus :
    decodeEvent malformedTodoStatusExampleJson = .error (.unsupportedTag
      [.field "data", .field "todos", .index 0, .field "status"] "blocked") := by
  rfl

/-- The seed marker has an empty payload; extra fields are not silently discarded. -/
theorem reject_sessionEndSeed_nonempty :
    decodeEvent malformedSessionEndSeedExampleJson = .error (.unsupportedField
      [.field "data"] "unexpected") := by
  rfl

theorem reject_replacement_incompleteCoverage :
    surfaceValidationSummary (validateJsonLog malformedReplacementMessageExampleJson) = none := by
  decide

/-! Reasoning chunks are retained as log-only payloads rather than silently projected to text. -/

def assistantChunkSummary : Except DecodeError WireEvent → Option (Nat × Nat × String)
  | .ok event =>
      match event.payload with
      | .assistantChunk chunk => some (chunk.turn.value, chunk.step.value, chunk.text)
      | .assistantReasoningChunk chunk => some (chunk.turn.value, chunk.step.value, chunk.text)
      | _ => none
  | .error _ => none

theorem accept_assistantChunk_reasoning :
    assistantChunkSummary (decodeEvent malformedAssistantChunkExampleJson) =
      some (1, 1, "hidden") := by
  decide

/-- The restricted text-delta projection admits only the source's first block index. -/
theorem reject_assistantChunk_nonzeroIndex :
    decodeEvent malformedAssistantChunkIndexExampleJson = .error (.unsupportedTag
      [.field "data", .field "chunk", .field "index"] "1") := by
  rfl

/-- Header fields without a local lossless representation are rejected explicitly. -/
theorem reject_requestHeader_temperature :
    decodeEvent malformedRequestHeaderExampleJson = .error (.unsupportedField
      [.field "data", .field "header", .field "config"] "temperature") := by
  rfl

/-- Assistant reasoning blocks remain outside the text-only session projection. -/
theorem reject_assistantReasoningBlock :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "assistant/message"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [
        ("turn", .num 1), ("step", .num 1),
        ("message", Lean.Json.mkObj [
          ("id", .str "assistant-1"), ("role", .str "assistant"),
          ("source", Lean.Json.mkObj [
            ("kind", .str "model"), ("provider", .str "deepseek"),
            ("model", .str "deepseek-reasoner")
          ]),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "reasoning"), ("text", .str "hidden")
          ]])
        ])
      ]),
      ("surfaceOp", .str "append")
    ]) = .error (.unsupportedTag
      [.field "data", .field "message", .field "content", .index 0, .field "type"] "reasoning") :=
  rfl

/-- Log-only boundary events cannot smuggle conditional surface metadata into the local log. -/
theorem reject_surfaceMetadataOnStepStart :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "step/start"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)]),
      ("surfaceOp", .str "append")
    ]) = .error (.unsupportedField [] "surfaceOp") :=
  rfl

/-- Core events marked skippable are rejected because local reconstruction cannot preserve it. -/
theorem reject_ignorableCoreEvent :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [("turn", .num 1)]),
      ("ignorable", .bool true)
    ]) = .error (.unsupportedField [] "ignorable") :=
  rfl

/-- An upstream abort cause has more structure than the local supported reason subset. -/
theorem reject_unmodeledTurnEndReason :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "turn/end"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [
        ("turn", .num 1),
        ("reason", Lean.Json.mkObj [
          ("kind", .str "aborted"),
          ("reason", Lean.Json.mkObj [("kind", .str "user")])
        ])
      ])
    ]) = .error (.unsupportedTag
      [.field "data", .field "reason", .field "kind"] "aborted") :=
  rfl

/-- An upstream zero step has no predecessor under the named one-to-zero normalization. -/
theorem reject_zeroStep :
    let event : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .stepStart { value := 1, safe := by decide }
        { value := 0, safe := by decide }
    }
    refineEvent State.initial event = .error .zeroStep := by
  rfl

/-- A tool result whose nested source and block ids disagree is never assigned a local id. -/
theorem reject_mismatchedToolResultIds :
    let result : WireToolResult := {
      turn := { value := 1, safe := by decide }
      step := { value := 1, safe := by decide }
      messageId := "m"
      sourceCallId := "source"
      blockCallId := "block"
      content := "result"
      isError := false
      sourceEventSeqs := []
      surfaceOp := .append
    }
    let wire : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .toolResult result
    }
    refineEvent State.initial wire =
      .error (.mismatchedToolResultIds "source" "block") := by
  rfl

/-- A turn-end next-step value cannot be invented when the validated prefix is not in a turn. -/
theorem reject_underdeterminedTurnEnd :
    let wire : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .turnEnd { value := 1, safe := by decide } .completed
    }
    refineEvent State.initial wire =
      .error (.cannotDeriveTurnEndStep (.ready 1)) := by
  rfl

end Cordis.SessionRefinement
