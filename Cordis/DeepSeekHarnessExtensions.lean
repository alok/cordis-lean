import Cordis.DeepSeekHarness

/-!
# Extension-preserving DeepSeek request construction

`DeepSeekHarness` historically specialized request construction to
`Session.noExtensions`.  The session kernel is more expressive: an
`ExtensionSchema` can add log-only or surface-visible event kinds while keeping
the surface projection indexed and certified.  This module lifts the request
boundary to an arbitrary schema.

The adapter reads only `Session.messages`, so custom log-only events remain in
the append-only log without leaking into a model request, while custom surface
events contribute the schema-provided `Message`.  It also carries complete and
streaming request-mode certificates and appends a validated assistant view without
changing the schema.  The result is still a pure JSON-AST/request-plan boundary.
It does not claim extension JSON decoding, provider compatibility, persistence,
transport, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessExtensions

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner

/-! ## Generic schema-indexed request adapter -/

def buildChatRequestFor
    {schema : Session.ExtensionSchema}
    (source : RequestSource)
    (session : Session.Session schema) :
    Except RequestError ChatRequest := do
  let converted ←
    sessionMessagesToChatMessagesWith source.errorToolResults session.messages
  let messages ←
    match source.system with
    | none => nonemptyMessages converted
    | some system =>
        .ok { head := .system system, tail := converted }
  .ok {
    model := source.model
    messages
    thinking := source.thinking
    reasoningEffort := source.reasoningEffort
    maxTokens := source.maxTokens
    responseFormat := source.responseFormat
    tools := source.tools
    toolChoice := source.toolChoice
  }

def buildRequestPlanFor
    {schema : Session.ExtensionSchema}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session schema) :
    Except RequestError RequestPlan := do
  let request ← buildChatRequestFor source session
  .ok (buildRequest baseUrl apiKey request)

def buildTypedRequestPlanFor
    {schema : Session.ExtensionSchema}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session schema) :
    Except RequestError (TypedRequestPlan .complete) := do
  let request ← buildChatRequestFor source session
  .ok (buildTypedCompleteRequest baseUrl apiKey request)

def buildStreamingRequestPlanFor
    {schema : Session.ExtensionSchema}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session schema) :
    Except RequestError RequestPlan := do
  let request ← buildChatRequestFor source session
  .ok (buildStreamingRequest baseUrl apiKey request)

def buildTypedStreamingRequestPlanFor
    {schema : Session.ExtensionSchema}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session schema) :
    Except RequestError (TypedRequestPlan .streaming) := do
  let request ← buildChatRequestFor source session
  .ok (buildTypedStreamingRequest baseUrl apiKey request)

theorem buildTypedStreamingRequestPlanFor_source_stream
    {schema : Session.ExtensionSchema}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session schema)
    {plan : TypedRequestPlan .streaming}
    (_plan_eq : buildTypedStreamingRequestPlanFor baseUrl apiKey source session = .ok plan) :
    plan.source.stream = true := by
  exact plan.streaming_source_stream

/-! ## Schema-preserving assistant append -/

def appendAssistantFor
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (turn step : Nat)
    (view : RichStream.AssistantMessageView)
    (assignment : StreamSession.CallIdAssignment view)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session schema :=
  session.appendSurface .assistantMessage
    (StreamSession.toAssistantPayload turn step view assignment)
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendAssistantFor_messages
    {schema : Session.ExtensionSchema}
    (session : Session.Session schema)
    (turn step : Nat)
    (view : RichStream.AssistantMessageView)
    (assignment : StreamSession.CallIdAssignment view)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendAssistantFor session turn step view assignment sourceEventSeqs
      sourcesNodup sourcesEarlier).messages =
      session.messages ++ [.assistant view.content
        (StreamSession.toSessionToolCalls view assignment)] := by
  simp [appendAssistantFor, StreamSession.toAssistantPayload,
    Session.Session.appendSurface, Session.Session.append, Session.Session.messages_eq_surface]

/-! ## Schema-indexed terminal runner -/

structure ExtensionRunner (schema : Session.ExtensionSchema) where
  session : Session.Session schema
  turn : Nat
  step : Nat
  nextCall : Nat
  nextSeq_eq_step : session.nextSeq = step
  toolCallCount_eq_nextCall : toolCallCount session.messages = nextCall

namespace ExtensionRunner

def empty (schema : Session.ExtensionSchema) (turn : Nat := 1) : ExtensionRunner schema where
  session := Session.Session.empty schema
  turn
  step := 0
  nextCall := 0
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := by rfl

def appendFinished
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    ExtensionRunner schema :=
  let view := finished.finished.view
  let assignment := sequentialAssignment runner.nextCall view
  let session := appendAssistantFor runner.session runner.turn runner.step view assignment
    sourceEventSeqs sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + view.rawToolCalls.length
    nextSeq_eq_step := by
      change runner.session.nextSeq + 1 = runner.step + 1
      rw [runner.nextSeq_eq_step]
    toolCallCount_eq_nextCall := by
      have messages_eq := appendAssistantFor_messages runner.session runner.turn runner.step view
        assignment sourceEventSeqs sourcesNodup sourcesEarlier
      simp only [session, messages_eq]
      rw [toolCallCount_append]
      rw [runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendFinished_messages
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant finished.finished.view.content
        (StreamSession.toSessionToolCalls finished.finished.view
          (sequentialAssignment runner.nextCall finished.finished.view))] := by
  change (appendAssistantFor runner.session runner.turn runner.step finished.finished.view
      (sequentialAssignment runner.nextCall finished.finished.view)
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  exact appendAssistantFor_messages runner.session runner.turn runner.step
    finished.finished.view (sequentialAssignment runner.nextCall finished.finished.view)
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendFinished_nextSeq
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
  rfl

theorem appendFinished_nextCall
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + finished.finished.view.rawToolCalls.length := by
  rfl

def appendText
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DeepSeekSessionRunner.ResponseError (ExtensionRunner schema) :=
  match finishText body with
  | .error error => .error error
  | .ok finished =>
      .ok (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier)

end ExtensionRunner

/-! ## A concrete extension schema -/

inductive ExampleKind : Session.Visibility → Type where
  | heartbeat : ExampleKind .logOnly
  | banner : ExampleKind .surface

inductive ExamplePayload :
    {visibility : Session.Visibility} → ExampleKind visibility → Type where
  | heartbeat : ExamplePayload .heartbeat
  | banner : String → ExamplePayload .banner

def exampleSurfaceContent :
    (kind : ExampleKind .surface) → ExamplePayload kind → Session.Message
  | .banner, .banner text => .user ("extension:" ++ text)

def exampleSchema : Session.ExtensionSchema where
  Kind := ExampleKind
  Payload := ExamplePayload
  surfaceContent := exampleSurfaceContent

def exampleHeader : Session.RequestHeader where
  provider := "deepseek"
  model := "deepseek-chat"
  system := none
  toolSchemas := []

def extensionSession : Session.Session exampleSchema :=
  let empty := Session.Session.empty exampleSchema
  let heartbeat : Session.Kind exampleSchema .logOnly :=
    .custom ExampleKind.heartbeat
  let withHeartbeat := empty.appendLogOnly heartbeat .heartbeat
  let withHeader := withHeartbeat.appendLogOnly .requestHeader exampleHeader
  withHeader.appendSurface .userMessage { content := "hello" } [] (by simp) (by simp)

theorem extensionSession_messages :
    extensionSession.messages = [.user "hello"] := by
  rfl

theorem heartbeat_is_log_only :
    (extensionSession.events.head?.map Session.LoggedEvent.surfaceMessage) = some none := by
  rfl

def extensionRequest : Except RequestError ChatRequest :=
  buildChatRequestFor { model := "deepseek-chat" } extensionSession

def extensionMessageCount : Nat :=
  match extensionRequest with
  | .error _ => 0
  | .ok request => request.messages.tail.length + 1

def extensionRequestHasOneMessage : Bool := extensionMessageCount == 1

def extensionStreamingRequest : Except RequestError RequestPlan :=
  buildStreamingRequestPlanFor "https://api.example" {
    value := "test-key"
  } { model := "deepseek-chat" } extensionSession

def extensionTypedStreamingRequest :
    Except RequestError (TypedRequestPlan .streaming) :=
  buildTypedStreamingRequestPlanFor "https://api.example" {
    value := "test-key"
  } { model := "deepseek-chat" } extensionSession

def extensionView : RichStream.AssistantMessageView where
  content := "assistant"
  rawToolCalls := []

def extensionAssignment : StreamSession.CallIdAssignment extensionView where
  ids := []
  length_eq := rfl
  nodup := by simp

def extensionWithAssistant : Session.Session exampleSchema :=
  appendAssistantFor extensionSession 1 3 extensionView extensionAssignment [] (by simp) (by simp)

def extensionRunner : ExtensionRunner exampleSchema where
  session := extensionSession
  turn := 1
  step := 3
  nextCall := 0
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := by rfl

def extensionRunnerText :
    Except DeepSeekSessionRunner.ResponseError (ExtensionRunner exampleSchema) :=
  ExtensionRunner.appendText extensionRunner DeepSeekRichStream.exampleTextStreamBody []
    (by simp) (by simp)

theorem extensionRequest_ok : ∃ request, extensionRequest = .ok request := by
  exact ⟨_, rfl⟩

theorem extensionMessageCount_eq : extensionMessageCount = 1 := by
  rfl

theorem extensionRequestHasOneMessage_eq : extensionRequestHasOneMessage = true := by
  rfl

theorem extensionStreamingRequest_stream :
    ∃ request, extensionStreamingRequest = .ok request ∧ request.source.stream = true := by
  exact ⟨_, rfl, buildStreamingRequest_source_stream _ _ _⟩

theorem extensionTypedStreamingRequest_stream :
    ∃ plan, extensionTypedStreamingRequest = .ok plan ∧ plan.source.stream = true := by
  exact ⟨_, rfl, TypedRequestPlan.streaming_source_stream _⟩

theorem extensionWithAssistant_messages :
    extensionWithAssistant.messages = [.user "hello", .assistant "assistant" []] := by
  rfl

theorem extensionRequest_surface_exact :
    extensionRequest = .ok {
      model := "deepseek-chat"
      messages := { head := .user "hello", tail := [] }
      thinking := none
      reasoningEffort := none
      maxTokens := none
      responseFormat := none
      tools := []
      toolChoice := none
    } := by
  rfl

end Cordis.DeepSeekHarnessExtensions
