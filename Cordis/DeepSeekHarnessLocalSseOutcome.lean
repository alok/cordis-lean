import Cordis.DeepSeekCurlIncrementalOutcome
import Cordis.DeepSeekHarnessLocalSse

/-!
# Loopback HTTP/SSE terminal outcomes into the typed conversation runner

This module composes the existing one-shot loopback SSE server with the incremental terminal
outcome validator. The real curl process sends a typed `stream: true` request; the response body is
retained with its line observations and strict wire certificate; then provider failures remain a
typed no-op while successful text/tool/mixed/multi outcomes are finished and appended to the
indexed `ConversationRunner`.

The result keeps request provenance, the dependent body-indexed outcome, dispatch endpoint, request
report, and server exit evidence together. It is local process/HTTP evidence only: it does not
establish remote reachability, TLS or credential authenticity, byte framing, backpressure,
cancellation, reconnects, provider-complete assembly, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlIncrementalOutcome
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekTerminalOutcome

structure PreparedOutcomeRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedOutcomeRequest

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedOutcomeRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedOutcomeRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedOutcomeRequest

inductive OutcomeDispatch (body : String) where
  | providerFailure
      (validated : DeepSeekStreamFailure.ValidatedFailureStream body)
      (runner : ConversationRunner)
  | appended
      (finished : FinishedResponse body)
      (runner : ConversationRunner)

inductive LocalOutcomeError where
  | emptyBody
  | request (error : RequestError)
  | transport (error : IncrementalOutcomeError)
  | dispatch (error : DeepSeekSessionRunner.ResponseError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

def dispatchOutcome
    {body : String}
    (runner : ConversationRunner)
    (outcome : TerminalOutcome body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DeepSeekSessionRunner.ResponseError (OutcomeDispatch body) :=
  match outcome with
  | .failure validated => .ok (.providerFailure validated runner)
  | .text validated =>
      match finishResponse (.text validated) with
      | .error error => .error (.terminal error)
      | .ok finished =>
          .ok (.appended finished
            (ConversationRunner.appendFinished runner finished sourceEventSeqs
              sourcesNodup sourcesEarlier))
  | .tool validated =>
      match finishResponse (.tool validated) with
      | .error error => .error (.terminal error)
      | .ok finished =>
          .ok (.appended finished
            (ConversationRunner.appendFinished runner finished sourceEventSeqs
              sourcesNodup sourcesEarlier))
  | .mixed validated =>
      match finishResponse (.mixed validated) with
      | .error error => .error (.terminal error)
      | .ok finished =>
          .ok (.appended finished
            (ConversationRunner.appendFinished runner finished sourceEventSeqs
              sourcesNodup sourcesEarlier))
  | .multi validated =>
      match finishResponse (.multi validated) with
      | .error error => .error (.terminal error)
      | .ok finished =>
          .ok (.appended finished
            (ConversationRunner.appendFinished runner finished sourceEventSeqs
              sourcesNodup sourcesEarlier))

structure OutcomeResult
    (source : RequestSource)
    (runner : ConversationRunner)
    (body : String) where
  port : Nat
  prepared : PreparedOutcomeRequest (localBaseUrl port) source runner
  response : IncrementalResponse body
  processed : ProcessedOutcome body
  dispatch : OutcomeDispatch body
  dispatch_eq : dispatchOutcome runner processed.outcome [] (by simp) (by simp) = .ok dispatch
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace OutcomeResult

theorem streaming_mode
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : OutcomeResult source runner body) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem outcome_exact
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : OutcomeResult source runner body) :
    validateTerminalOutcome body = .ok result.processed.outcome :=
  result.processed.outcome_exact

theorem server_exited_successfully
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : OutcomeResult source runner body) :
    result.serverExit = 0 :=
  result.server_exit_eq

theorem provider_failure_endpoint
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : OutcomeResult source runner body)
    {validated : DeepSeekStreamFailure.ValidatedFailureStream body}
    (h : result.dispatch = .providerFailure validated runner) :
    result.dispatch = .providerFailure validated runner :=
  h

end OutcomeResult

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

private def serverArgs (body : String) : Array String :=
  #[("-u" : String), "-c", sseServerScript, body]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

private def prepare
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey) :
    Except RequestError (PreparedOutcomeRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by
  simp

private theorem emptySourcesEarlier
    (runner : ConversationRunner) :
    ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxReads : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalOutcomeError
      (Sigma fun body : String => OutcomeResult source runner body)) := do
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
            match ← executeOutcome maxReads (curlProcess {}) prepared.plan.request
                (fun _ _ => pure ()) with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.transport error))
        | .ok ⟨responseBody, processed⟩ =>
            let serverExit ← child.wait
            let serverStderr ← IO.ofExcept stderrTask.get
            let reportLine ← stdout.getLine
            match parseReport reportLine with
            | none => pure (.error (.report reportLine))
            | some (requests, validRequests) =>
                match hDispatch : dispatchOutcome runner processed.outcome [] emptySourcesNodup
                    (emptySourcesEarlier runner) with
                | .error error => pure (.error (.dispatch error))
                | .ok dispatch =>
                    if hExit : serverExit = 0 then
                      pure (.ok ⟨responseBody, {
                        port
                        prepared
                        response := processed.response
                        processed
                        dispatch
                        dispatch_eq := hDispatch
                        requests
                        validRequests
                        serverExit
                        serverStderr
                        server_exit_eq := hExit
                      }⟩)
                    else
                      pure (.error (.server serverExit serverStderr))
  catch error =>
    stopServer child stderrTask
    pure (.error (.io (toString error)))

def runWithKey
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (maxReads : Nat := 64) :
    IO (Except LocalOutcomeError
      (Sigma fun responseBody : String => OutcomeResult source runner responseBody)) := do
  if body.isEmpty then
    pure (.error .emptyBody)
  else
    try
      let child ← IO.Process.spawn {
        cmd := "python3"
        args := serverArgs body
        stdin := serverStdio.stdin
        stdout := serverStdio.stdout
        stderr := serverStdio.stderr
      }
      let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
      runChild source runner key maxReads child stderrTask
    catch error =>
      pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner := DeepSeekHarnessLocalSse.Example.runner

def failureBody : String := DeepSeekStreamFailure.exampleContentFilterBody

def textBody : String := DeepSeekRichStream.exampleTextStreamBody

def toolBody : String := DeepSeekRichToolStream.exampleToolStreamBody

def mixedBody : String := DeepSeekRichMixedStream.mixedStreamBody

def multiBody : String := DeepSeekRichMultiStream.multiBody

def failureRun : IO (Except LocalOutcomeError
    (Sigma fun body : String => OutcomeResult DeepSeekHarness.counterRequestSource runner body)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } failureBody 64

def textRun : IO (Except LocalOutcomeError
    (Sigma fun body : String => OutcomeResult DeepSeekHarness.counterRequestSource runner body)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } textBody 64

def toolRun : IO (Except LocalOutcomeError
    (Sigma fun body : String => OutcomeResult DeepSeekHarness.counterRequestSource runner body)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } toolBody 64

def mixedRun : IO (Except LocalOutcomeError
    (Sigma fun body : String => OutcomeResult DeepSeekHarness.counterRequestSource runner body)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } mixedBody 64

def multiRun : IO (Except LocalOutcomeError
    (Sigma fun body : String => OutcomeResult DeepSeekHarness.counterRequestSource runner body)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } multiBody 64

end Example

end Cordis.DeepSeekHarnessLocalSseOutcome
