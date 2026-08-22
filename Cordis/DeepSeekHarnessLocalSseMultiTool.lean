import Cordis.DeepSeekHarnessLocalSse
import Cordis.DeepSeekStreamHarness

/-!
# Loopback HTTP SSE multi-tool conversation

This module composes the real loopback HTTP/SSE request boundary with the complete streamed
multi-tool conversation runner.  The fixture validates the typed request, emits two streamed
function calls, and the dependent harness assigns local call IDs, executes both calls, and
appends both certified tool results to the indexed session.

The result is local process/HTTP evidence only.  It does not establish provider-complete
assembly, backpressure, blocked-read cancellation, reconnect policy, credential or TLS
authenticity, arbitrary process cleanup, or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseMultiTool

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

structure PreparedMultiToolRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedMultiToolRequest

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedMultiToolRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedMultiToolRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedMultiToolRequest

inductive LocalSseMultiToolError where
  | request (error : RequestError)
  | round (error : StreamConversationError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalSseMultiToolResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (source : RequestSource)
    (before : Model)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedMultiToolRequest (localBaseUrl port) source runner
  body : String
  round : StreamConversationRoundResult cfg before body
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalSseMultiToolResult

theorem streaming_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolResult cfg source before runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolResult cfg source before runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSseMultiToolResult

private def serverArgs : Array String :=
  #[("-u" : String), "-c", sseServerScript, counterMultiToolStreamBody]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

private def stopServer {config : IO.Process.StdioConfig}
    (child : IO.Process.Child config)
    (stderrTask : Task (Except IO.Error String)) : IO Unit := do
  try
    child.kill
  catch _ =>
    pure ()
  try
    discard <| child.wait
  catch _ =>
    pure ()
  try
    discard <| IO.ofExcept stderrTask.get
  catch _ =>
    pure ()

private def prepare
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey) :
    Except RequestError (PreparedMultiToolRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private def runChild
    {Model Capability : Type}
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseMultiToolError
      (LocalSseMultiToolResult cfg source before runner)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        let baseUrl := localBaseUrl port
        match prepare baseUrl source runner key with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.request error))
        | .ok prepared =>
            match ← executeConversationMultiStreamRound
                (curlProcess { extraArgs := #["--no-buffer"] }) baseUrl key source cfg before runner
                [] (by simp) (by simp) with
            | .error error =>
                stopServer child stderrTask
                pure (.error (.round error))
            | .ok ⟨body, round⟩ =>
                let serverExit ← child.wait
                let serverStderr ← IO.ofExcept stderrTask.get
                let reportLine ← stdout.getLine
                match parseReport reportLine with
                | none => pure (.error (.report reportLine))
                | some (requests, validRequests) =>
                    if hExit : serverExit = 0 then
                      pure (.ok {
                        port
                        prepared
                        body
                        round
                        requests
                        validRequests
                        serverExit
                        serverStderr
                        server_exit_eq := hExit
                      })
                    else
                      pure (.error (.server serverExit serverStderr))
  catch error =>
    stopServer child stderrTask
    pure (.error (.io (toString error)))

def runWithKey
    {Model Capability : Type}
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalSseMultiToolError
      (LocalSseMultiToolResult cfg source before runner)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild source cfg before runner key child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def run : IO (Except LocalSseMultiToolError
    (LocalSseMultiToolResult Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithKey DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 runner
    { value := "fixture-key" }

structure Summary where
  requests : Nat
  validRequests : Nat
  toolCalls : Nat
  executions : Nat
  finalNextSeq : Nat
  finalModel : Nat
deriving BEq, DecidableEq, Repr

def summarize (result : LocalSseMultiToolResult Cordis.Harness.counterConfig
    DeepSeekHarness.counterRequestSource 0 runner) : Summary := {
  requests := result.requests
  validRequests := result.validRequests
  toolCalls := result.round.finished.finished.view.rawToolCalls.length
  executions := result.round.executions.length
  finalNextSeq := result.round.runner.session.nextSeq
  finalModel := result.round.finalModel
}

def expectedSummary : Summary := {
  requests := 1
  validRequests := 1
  toolCalls := 2
  executions := 2
  finalNextSeq := 4
  finalModel := 0
}

theorem expectedSummary_two_calls : expectedSummary.toolCalls = 2 := rfl

theorem expectedSummary_two_executions : expectedSummary.executions = 2 := rfl

end Example

end Cordis.DeepSeekHarnessLocalSseMultiTool
