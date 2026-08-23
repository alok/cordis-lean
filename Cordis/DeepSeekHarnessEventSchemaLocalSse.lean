import Cordis.DeepSeekHarnessEventToolSchema
import Cordis.DeepSeekHarnessLocalSse

/-!
# Source-preserving current-Harness schemas through local SSE

`DeepSeekHarnessEventToolSchema` attaches a validated, source-preserving tool-schema list to the
request endpoint, while `DeepSeekHarnessEventLocalSse` exercises the compressed structural request
projection.  This module carries the same validated event endpoint through a real loopback SSE
request whose outgoing tool definitions retain the original JSON-schema object as
`ToolDefinition.function.parameters`.

The raw source is intentionally rebuilt from the dependent schema certificate instead of being
silently identified with the compressed `Session.ToolSchema` projection.  The result therefore
proves the exact names, descriptions, parameters, request model, stream flag, response frames,
and append endpoint used by this local run.  It remains local process/HTTP evidence: credentials,
provider obedience, network authenticity, persistence, cancellation, reconnects, and equivalence
with the deployed TypeScript Harness remain external.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventSchemaLocalSse

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventRequest
open Cordis.DeepSeekHarnessEventToolSchema
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRequest
open Cordis.DeepSeekSessionRunner
open Cordis.SessionRefinement

def rawToolDefinition (source : WireRequestToolSchemaSource) : ToolDefinition := {
  function := {
    name := source.name
    description := some source.description
    parameters := source.parameters
    strict := none
  }
}

def rawRequestSource
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) : RequestSource := {
  model := certificate.base.request.header.model
  system := certificate.base.request.header.system
  thinking := options.thinking
  reasoningEffort := options.reasoningEffort
  maxTokens := options.maxTokens
  responseFormat := options.responseFormat
  tools := sources.map rawToolDefinition
  toolChoice := options.toolChoice
  errorToolResults := options.errorToolResults
}

def rawRunner
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    ConversationRunner := {
  session := certificate.base.log.final.session
  turn := 1
  step := certificate.base.log.final.session.nextSeq
  nextCall := toolCallCount certificate.base.log.final.session.messages
  toolCallCount_eq_nextCall := rfl
}

theorem rawSource_model
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRequestSource certificate).model = certificate.base.request.header.model := by
  rfl

theorem rawSource_system
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRequestSource certificate).system = certificate.base.request.header.system := by
  rfl

theorem rawSource_tool_names
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRequestSource certificate).tools.map (fun tool => tool.function.name) =
      sources.map WireRequestToolSchemaSource.name := by
  simp [rawRequestSource, rawToolDefinition]

theorem rawSource_tool_descriptions
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRequestSource certificate).tools.map (fun tool => tool.function.description) =
      sources.map (fun source => some source.description) := by
  simp [rawRequestSource, rawToolDefinition]

theorem rawSource_tool_parameters
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRequestSource certificate).tools.map (fun tool => tool.function.parameters) =
      sources.map WireRequestToolSchemaSource.parameters := by
  simp [rawRequestSource, rawToolDefinition]

theorem rawRunner_session
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    (rawRunner certificate).session = certificate.base.log.final.session := by
  rfl

structure SchemaLocalSseResult
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) where
  localResult : LocalSseResult (rawRequestSource certificate) (rawRunner certificate)

private theorem buildChatRequest_fields_of_ok
    (source : RequestSource)
    (session : Cordis.Session.Session Cordis.Session.noExtensions)
    {request : ChatRequest}
    (h : buildChatRequest source session = .ok request) :
    request.model = source.model ∧ request.tools = source.tools := by
  unfold buildChatRequest at h
  generalize hconverted :
      sessionMessagesToChatMessagesWith source.errorToolResults
        (requestSourceMessages source session) = converted at h
  cases hsystem : source.system with
  | none =>
      rw [hsystem] at h
      cases converted with
      | error error =>
          dsimp at h
          cases h
      | ok messages =>
          dsimp at h
          change (do
            let messageList ← nonemptyMessages messages
            Except.ok {
              model := source.model, messages := messageList, thinking := source.thinking,
              reasoningEffort := source.reasoningEffort, maxTokens := source.maxTokens,
              responseFormat := source.responseFormat, tools := source.tools,
              toolChoice := source.toolChoice }) = Except.ok request at h
          cases hne : nonemptyMessages messages with
          | error error =>
              rw [hne] at h
              change Except.error error = Except.ok request at h
              cases h
          | ok messageList =>
              rw [hne] at h
              change Except.ok {
                model := source.model, messages := messageList, thinking := source.thinking,
                reasoningEffort := source.reasoningEffort, maxTokens := source.maxTokens,
                responseFormat := source.responseFormat, tools := source.tools,
                toolChoice := source.toolChoice } = Except.ok request at h
              injection h with hrequest
              constructor
              · exact (congrArg ChatRequest.model hrequest).symm
              · exact (congrArg ChatRequest.tools hrequest).symm
  | some system =>
      rw [hsystem] at h
      cases converted with
      | error error =>
          dsimp at h
          cases h
      | ok converted =>
          dsimp at h
          change (do
            let messages ← Except.ok {head := ChatMessage.system system, tail := converted}
            Except.ok {
              model := source.model, messages := messages, thinking := source.thinking,
              reasoningEffort := source.reasoningEffort, maxTokens := source.maxTokens,
              responseFormat := source.responseFormat, tools := source.tools,
              toolChoice := source.toolChoice }) = Except.ok request at h
          change Except.ok {
            model := source.model,
            messages := {head := ChatMessage.system system, tail := converted},
            thinking := source.thinking,
            reasoningEffort := source.reasoningEffort, maxTokens := source.maxTokens,
            responseFormat := source.responseFormat, tools := source.tools,
            toolChoice := source.toolChoice } = Except.ok request at h
          injection h with hrequest
          constructor
          · exact (congrArg ChatRequest.model hrequest).symm
          · exact (congrArg ChatRequest.tools hrequest).symm

private theorem prepared_plan_source_eq
    {baseUrl : String}
    {source : RequestSource}
    {runner : ConversationRunner}
    {request : ChatRequest}
    (prepared : PreparedStreamingRequest baseUrl source runner)
    (request_eq : buildChatRequest source runner.session = .ok request) :
    prepared.plan.source = request.asStreaming := by
  have plan_eq := prepared.build_eq
  unfold buildTypedStreamingRequestPlan at plan_eq
  rw [request_eq] at plan_eq
  change Except.ok (buildTypedStreamingRequest baseUrl prepared.key request) =
    Except.ok prepared.plan at plan_eq
  have plan_eq' : buildTypedStreamingRequest baseUrl prepared.key request = prepared.plan := by
    injection plan_eq
  simpa [buildTypedStreamingRequest, buildTypedRequest, buildRequest] using
    (congrArg (fun plan : TypedRequestPlan .streaming => plan.source) plan_eq').symm

namespace SchemaLocalSseResult

theorem request_model
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.model = certificate.base.request.header.model := by
  cases requestResult : buildChatRequest (rawRequestSource certificate)
      (rawRunner certificate).session with
  | error error =>
      have plan_eq := result.localResult.prepared.build_eq
      unfold buildTypedStreamingRequestPlan at plan_eq
      rw [requestResult] at plan_eq
      contradiction
  | ok request =>
      rw [prepared_plan_source_eq result.localResult.prepared requestResult]
      have request_fields := buildChatRequest_fields_of_ok
        (rawRequestSource certificate) (rawRunner certificate).session requestResult
      exact request_fields.1.trans (rawSource_model certificate)

theorem request_tool_names
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.tools.map (fun tool => tool.function.name) =
      sources.map WireRequestToolSchemaSource.name := by
  cases requestResult : buildChatRequest (rawRequestSource certificate)
      (rawRunner certificate).session with
  | error error =>
      have plan_eq := result.localResult.prepared.build_eq
      unfold buildTypedStreamingRequestPlan at plan_eq
      rw [requestResult] at plan_eq
      contradiction
  | ok request =>
      rw [prepared_plan_source_eq result.localResult.prepared requestResult]
      have request_fields := buildChatRequest_fields_of_ok
        (rawRequestSource certificate) (rawRunner certificate).session requestResult
      simpa [ChatRequest.asStreaming, request_fields.2] using rawSource_tool_names certificate

theorem request_tool_descriptions
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.tools.map (fun tool => tool.function.description) =
      sources.map (fun source => some source.description) := by
  cases requestResult : buildChatRequest (rawRequestSource certificate)
      (rawRunner certificate).session with
  | error error =>
      have plan_eq := result.localResult.prepared.build_eq
      unfold buildTypedStreamingRequestPlan at plan_eq
      rw [requestResult] at plan_eq
      contradiction
  | ok request =>
      rw [prepared_plan_source_eq result.localResult.prepared requestResult]
      have request_fields := buildChatRequest_fields_of_ok
        (rawRequestSource certificate) (rawRunner certificate).session requestResult
      simpa [ChatRequest.asStreaming, request_fields.2] using
        rawSource_tool_descriptions certificate

theorem request_tool_parameters
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.tools.map (fun tool => tool.function.parameters) =
      sources.map WireRequestToolSchemaSource.parameters := by
  cases requestResult : buildChatRequest (rawRequestSource certificate)
      (rawRunner certificate).session with
  | error error =>
      have plan_eq := result.localResult.prepared.build_eq
      unfold buildTypedStreamingRequestPlan at plan_eq
      rw [requestResult] at plan_eq
      contradiction
  | ok request =>
      rw [prepared_plan_source_eq result.localResult.prepared requestResult]
      have request_fields := buildChatRequest_fields_of_ok
        (rawRequestSource certificate) (rawRunner certificate).session requestResult
      simpa [ChatRequest.asStreaming, request_fields.2] using
        rawSource_tool_parameters certificate

theorem stream_mode
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.stream = true :=
  result.localResult.prepared.streaming_mode

theorem append_endpoint
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.after = Cordis.DeepSeekStreamHarness.ConversationRunner.appendFinished
      (rawRunner certificate)
      result.localResult.finished [] (by simp) (by simp) :=
  result.localResult.append_eq

theorem final_next_seq
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (result : SchemaLocalSseResult certificate) :
    result.localResult.after.session.nextSeq =
      (rawRunner certificate).session.nextSeq + 1 :=
  LocalSseResult.nextSeq result.localResult

theorem source_header_tools
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    {certificate : PreparedSchemaLogRequest input encoder options sources}
    (_result : SchemaLocalSseResult certificate) :
    sources.map sourceToLocalTool = certificate.base.request.header.toolSchemas :=
  certificate.header_tools_eq

end SchemaLocalSseResult

def runWithKey
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources)
    (key : ApiKey)
    (body : String)
    (maxReads : Nat := 64) :
    IO (Except LocalSseError (SchemaLocalSseResult certificate)) := do
  match ← DeepSeekHarnessLocalSse.runWithKey
      (rawRequestSource certificate) (rawRunner certificate) key body maxReads with
  | .error error => pure (.error error)
  | .ok result => pure (.ok { localResult := result })

namespace Example

def certificate := headerSchemaAttachment.2

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except LocalSseError (SchemaLocalSseResult certificate)) :=
  runWithKey certificate { value := "fixture-key" } body 64

structure Summary where
  requests : Nat
  validRequests : Nat
  toolCount : Nat
  deliveredFrames : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
deriving BEq, DecidableEq, Repr

def summarize (result : SchemaLocalSseResult certificate) : Summary := {
  requests := result.localResult.requests
  validRequests := result.localResult.validRequests
  toolCount := result.localResult.prepared.plan.source.tools.length
  deliveredFrames := result.localResult.response.wire.frames.length
  initialNextSeq := (rawRunner certificate).session.nextSeq
  finalNextSeq := result.localResult.after.session.nextSeq
}

def expectedSummary : Summary := {
  requests := 1
  validRequests := 1
  toolCount := 1
  deliveredFrames := 3
  initialNextSeq := 6
  finalNextSeq := 7
}

theorem final_next_seq_expected (result : SchemaLocalSseResult certificate) :
    (summarize result).finalNextSeq = 7 := by
  change result.localResult.after.session.nextSeq = 7
  rw [SchemaLocalSseResult.final_next_seq result]
  rfl

theorem initial_next_seq_expected (result : SchemaLocalSseResult certificate) :
    (summarize result).initialNextSeq = 6 := by
  rfl

theorem tool_parameters_are_source_json (result : SchemaLocalSseResult certificate) :
    result.localResult.prepared.plan.source.tools.map
        (fun tool => tool.function.parameters) =
      [SessionRefinement.headerChunkParametersJson] := by
  rw [SchemaLocalSseResult.request_tool_parameters result]
  rfl

end Example

end Cordis.DeepSeekHarnessEventSchemaLocalSse
