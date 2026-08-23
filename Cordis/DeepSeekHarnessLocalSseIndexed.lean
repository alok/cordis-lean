import Cordis.DeepSeekHarnessLocalSse
import Cordis.DeepSeekSessionRequest

/-!
# Indexed session handoff over a real local HTTP/SSE fixture

`DeepSeekHarnessLocalSse` exercises the actual curl/loopback-server boundary, while
`DeepSeekSessionRequest` carries a schema-indexed request and a proof-producing request builder.
This module connects those two layers without asserting that the fixture's returned body is the
body supplied to the process.  The local result retains its own parsed body, wire frames, request
certificate, and conversation endpoint; the indexed wrapper adds the exact streaming-plan and
`ExtensionRunner.appendFinished` equations.

The fixture is intentionally local evidence only.  It says nothing about remote reachability,
TLS, credential validity, provider authenticity, persistence, reconnects, blocked reads, or
equivalence with a deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseIndexed

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekSessionRequest
open Cordis.DeepSeekSessionRunner

def fromConversation (runner : ConversationRunner) : ExtensionRunner Session.noExtensions where
  session := runner.session
  turn := runner.turn
  step := runner.session.nextSeq
  nextCall := runner.nextCall
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := runner.toolCallCount_eq_nextCall

theorem fromConversation_append
    (runner : ExtensionRunner Session.noExtensions)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    fromConversation
        (DeepSeekStreamHarness.ConversationRunner.appendFinished
          { session := runner.session, turn := runner.turn, step := runner.step,
            nextCall := runner.nextCall,
            toolCallCount_eq_nextCall := runner.toolCallCount_eq_nextCall }
          finished sourceEventSeqs sourcesNodup sourcesEarlier) =
    ExtensionRunner.appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier := by
  simp [fromConversation, ExtensionRunner.appendFinished,
    DeepSeekStreamHarness.ConversationRunner.appendFinished,
    DeepSeekHarnessExtensions.appendAssistantFor,
    StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, StreamSession.toAssistantPayload, runner.nextSeq_eq_step]

theorem streaming_plan_eq
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder)
    {baseUrl : String} {key : ApiKey} {plan : TypedRequestPlan .streaming}
    (h : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan) :
    buildStreamingPlan baseUrl key prepared = plan := by
  simp only [buildStreamingPlan, buildTypedStreamingRequestPlan] at h ⊢
  have hchat : buildChatRequest source runner.session = .ok prepared.chat := by
    have hchatFor := prepared.build_eq
    change buildChatRequestFor source runner.session = .ok prepared.chat at hchatFor
    change buildChatRequest source runner.session = .ok prepared.chat
    exact hchatFor
  rw [hchat] at h
  cases h
  rfl

theorem local_after_append
    {runner : ExtensionRunner Session.noExtensions}
    {source : RequestSource}
    (result : Cordis.DeepSeekHarnessLocalSse.LocalSseResult source
      { session := runner.session, turn := runner.turn, step := runner.step,
        nextCall := runner.nextCall,
        toolCallCount_eq_nextCall := runner.toolCallCount_eq_nextCall }) :
    fromConversation result.after =
      ExtensionRunner.appendFinished runner result.finished [] (by simp) (by simp) := by
  cases result with
  | mk port prepared body response finished after append_eq requests validRequests serverExit
      serverStderr server_exit_eq =>
    cases append_eq
    exact fromConversation_append runner finished [] (by simp) (by simp)

inductive IndexedLocalSseError where
  | local (error : Cordis.DeepSeekHarnessLocalSse.LocalSseError)
deriving DecidableEq, Repr

structure IndexedLocalSseResult
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder) where
  localResult : Cordis.DeepSeekHarnessLocalSse.LocalSseResult source
    { session := runner.session, turn := runner.turn, step := runner.step,
      nextCall := runner.nextCall,
      toolCallCount_eq_nextCall := runner.toolCallCount_eq_nextCall }
  plan_eq : buildStreamingPlan (Cordis.DeepSeekHarnessLocalSse.localBaseUrl
      localResult.port) localResult.prepared.key prepared = localResult.prepared.plan
  after : ExtensionRunner Session.noExtensions
  append_eq :
    after = ExtensionRunner.appendFinished runner localResult.finished [] (by simp) (by simp)

namespace IndexedLocalSseResult

theorem stream_mode
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    {prepared : PreparedRequest request source encoder}
    (result : IndexedLocalSseResult prepared) :
    result.localResult.prepared.plan.source.stream = true :=
  result.localResult.prepared.streaming_mode

theorem indexed_plan_exact
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    {prepared : PreparedRequest request source encoder}
    (result : IndexedLocalSseResult prepared) :
    buildStreamingPlan (Cordis.DeepSeekHarnessLocalSse.localBaseUrl
      result.localResult.port) result.localResult.prepared.key prepared =
      result.localResult.prepared.plan :=
  result.plan_eq

theorem append_endpoint_exact
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    {prepared : PreparedRequest request source encoder}
    (result : IndexedLocalSseResult prepared) :
    result.after = ExtensionRunner.appendFinished runner result.localResult.finished []
      (by simp) (by simp) :=
  result.append_eq

end IndexedLocalSseResult

def runWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder)
    (key : ApiKey)
    (body : String) :
    IO (Except IndexedLocalSseError (IndexedLocalSseResult prepared)) := do
  match ← Cordis.DeepSeekHarnessLocalSse.runWithKeyAndFinish finish source
      { session := runner.session, turn := runner.turn, step := runner.step,
        nextCall := runner.nextCall,
        toolCallCount_eq_nextCall := runner.toolCallCount_eq_nextCall }
      key body with
  | .error error => pure (.error (.local error))
  | .ok result =>
      pure (.ok {
        localResult := result
        plan_eq := streaming_plan_eq prepared result.prepared.build_eq
        after := fromConversation result.after
        append_eq := local_after_append result
      })

def runWithKey
    {runner : ExtensionRunner Session.noExtensions}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder)
    (key : ApiKey)
    (body : String) :
    IO (Except IndexedLocalSseError (IndexedLocalSseResult prepared)) :=
  runWithFinish finishText prepared key body

namespace Example

def initialHeader : Session.RequestHeader where
  provider := "deepseek"
  model := "deterministic-counter"
  system := none
  toolSchemas := []

def initialSession : Session.Session Session.noExtensions :=
  let empty := Session.Session.empty Session.noExtensions
  let headed := empty.appendLogOnly .requestHeader initialHeader
  headed.appendSurface .userMessage { content := "stream me" } [] (by simp) (by simp)

def initialRunner : ExtensionRunner Session.noExtensions where
  session := initialSession
  turn := 1
  step := initialSession.nextSeq
  nextCall := 0
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := by rfl

def encoder : ToolSchemaEncoder where
  encode schema := {
    function := {
      name := schema.name
      description := some schema.description
      parameters := .str schema.inputSchema
      strict := none
    }
  }
  name_eq _schema := rfl
  description_eq _schema := rfl

def request : Session.ModelRequest initialRunner.session :=
  match h : Session.mkRequest initialRunner.session with
  | none => nomatch h
  | some request => request

def source : RequestSource := sourceFor request encoder {}

def prepared : PreparedRequest request source encoder :=
  match h : prepare request source encoder (sourceFor_agreement request encoder {}) with
  | .error _error => nomatch h
  | .ok prepared => prepared

theorem prepared_model : prepared.chat.model = "deterministic-counter" := by
  exact PreparedRequest.chat_model_eq_header prepared

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except IndexedLocalSseError (IndexedLocalSseResult prepared)) :=
  runWithKey prepared { value := "fixture-key" } body

structure Summary where
  requests : Nat
  validRequests : Nat
  deliveredFrames : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
deriving BEq, DecidableEq, Repr

def summarize (result : IndexedLocalSseResult prepared) : Summary := {
  requests := result.localResult.requests
  validRequests := result.localResult.validRequests
  deliveredFrames := result.localResult.response.wire.frames.length
  initialNextSeq := initialRunner.session.nextSeq
  finalNextSeq := result.after.session.nextSeq
}

def summaryIO : IO Summary := do
  match ← run with
  | .error _error =>
      throw (IO.userError "indexed local SSE failed")
  | .ok result =>
      pure (summarize result)

def expectedSummary : Summary := {
  requests := 1
  validRequests := 1
  deliveredFrames := 3
  initialNextSeq := 2
  finalNextSeq := 3
}

theorem summary_eq (result : IndexedLocalSseResult prepared) :
    summarize result = {
      requests := result.localResult.requests
      validRequests := result.localResult.validRequests
      deliveredFrames := result.localResult.response.wire.frames.length
      initialNextSeq := initialRunner.session.nextSeq
      finalNextSeq := result.after.session.nextSeq
    } := rfl

end Example

end Cordis.DeepSeekHarnessLocalSseIndexed
