import Cordis.DeepSeekHarnessLocalSseApiError

/-!
# Loopback API-error retry into the typed conversation runner

This module composes the real loopback status-error fixture with one explicit retry. The first
valid streaming request receives an HTTP 429 and a dependent `ValidatedApiError`; the second valid
request receives a strict SSE success body and only that accepted response is dispatched into the
indexed runner. The result keeps both dependent bodies, the first transport/error certificate,
the accepted outcome, request counts, and clean process evidence.

This is a bounded local retry witness, not a provider policy theorem. Backoff, idempotency of
external effects, cancellation, reconnects, credentials, TLS, and deployed equivalence remain
caller/runtime obligations.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseApiErrorRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiErrorEnvelope
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlIncrementalOutcome
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseOutcome
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekTerminalOutcome

def apiErrorRetryServerScript : String :=
  "import http.server,json,sys\n" ++
  "error_body=sys.argv[1].encode()\n" ++
  "success_body=sys.argv[2].encode()\n" ++
  "class H(http.server.BaseHTTPRequestHandler):\n" ++
  "  count=0\n" ++
  "  valid=0\n" ++
  "  def do_POST(self):\n" ++
  "    n=int(self.headers.get('Content-Length','0'))\n" ++
  "    raw=self.rfile.read(n)\n" ++
  "    try:\n" ++
  "      request=json.loads(raw.decode())\n" ++
  "      good=self.path=='/chat/completions' and self.command=='POST' and " ++
  "self.headers.get('Authorization')=='Bearer fixture-key' and " ++
  "request.get('model')=='deterministic-counter' and request.get('stream') is True\n" ++
  "    except Exception:\n" ++
  "      good=False\n" ++
  "    H.count += 1\n" ++
  "    if good:\n" ++
  "      H.valid += 1\n" ++
  "    if good and H.count == 1:\n" ++
  "      payload=error_body\n" ++
  "      status=429\n" ++
  "      content='application/json'\n" ++
  "    elif good and H.count == 2:\n" ++
  "      payload=success_body\n" ++
  "      status=200\n" ++
  "      content='text/event-stream'\n" ++
  "    else:\n" ++
  "      payload=b'{\"error\":{\"message\":\"fixture request mismatch\"," ++
  "\"type\":\"invalid_request_error\",\"param\":null,\"code\":\"400\"}}'\n" ++
  "      status=400\n" ++
  "      content='application/json'\n" ++
  "    self.send_response(status)\n" ++
  "    self.send_header('Content-Type',content)\n" ++
  "    self.send_header('Content-Length',str(len(payload)))\n" ++
  "    self.end_headers()\n" ++
  "    if status == 200:\n" ++
  "      for line in payload.splitlines(True):\n" ++
  "        self.wfile.write(line)\n" ++
  "        self.wfile.flush()\n" ++
  "    else:\n" ++
  "      self.wfile.write(payload)\n" ++
  "      self.wfile.flush()\n" ++
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "server.handle_request()\n" ++
  "server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

inductive LocalApiErrorRetryError where
  | emptyBody
  | request (error : RequestError)
  | firstTransport (error : IncrementalError)
  | firstSuccess (body : String)
  | firstStatus (status : Nat)
  | firstEnvelope (error : DeepSeekApiErrorEnvelope.ValidationError)
  | secondTransport (error : IncrementalError)
  | secondOutcome (error : TerminalOutcomeError)
  | secondDispatch (error : DeepSeekSessionRunner.ResponseError)
  | counts (requests : Nat) (validRequests : Nat)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure ApiErrorRetryResult
    (source : RequestSource)
    (runner : ConversationRunner)
    (errorBody : String)
    (successBody : String) where
  firstStatus : Nat
  firstValidated : ValidatedApiError errorBody
  firstTransportError : IncrementalError
  first_status_eq : firstStatus = 429
  first_transport_error_eq : firstTransportError = .httpStatus firstStatus errorBody
  accepted : OutcomeResult source runner successBody
  attempts : Nat
  attempts_eq : attempts = 2
  requests_eq : accepted.requests = 2
  valid_requests_eq : accepted.validRequests = 2

namespace ApiErrorRetryResult

theorem first_status_is_rate_limited
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    result.firstStatus = 429 :=
  result.first_status_eq

theorem first_body_is_validated
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    Lean.Json.parse errorBody = .ok result.firstValidated.json :=
  result.firstValidated.parsed

theorem first_decodes_api_error
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    decodeResponseJson result.firstValidated.json =
      .error (.api result.firstValidated.error) :=
  result.firstValidated.decoded

theorem first_transport_is_http_status
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    result.firstTransportError = .httpStatus result.firstStatus errorBody :=
  result.first_transport_error_eq

theorem attempts_are_two
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    result.attempts = 2 :=
  result.attempts_eq

theorem requests_are_two
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    result.accepted.requests = 2 ∧ result.accepted.validRequests = 2 :=
  ⟨result.requests_eq, result.valid_requests_eq⟩

theorem accepted_outcome_exact
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    validateTerminalOutcome successBody = .ok result.accepted.processed.outcome :=
  result.accepted.processed.outcome_exact

theorem accepted_server_exited
    {source : RequestSource} {runner : ConversationRunner}
    {errorBody successBody : String}
    (result : ApiErrorRetryResult source runner errorBody successBody) :
    result.accepted.serverExit = 0 :=
  result.accepted.server_exit_eq

end ApiErrorRetryResult

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

private def serverArgs (errorBody successBody : String) : Array String :=
  #[
    ("-u" : String),
    "-c",
    apiErrorRetryServerScript,
    errorBody,
    successBody
  ]

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

private def finishAccepted
    (port : Nat)
    {source : RequestSource}
    {runner : ConversationRunner}
    {errorBody : String}
    (firstStatus : Nat)
    (first_status_eq : firstStatus = 429)
    (firstValidated : ValidatedApiError errorBody)
    (prepared : PreparedOutcomeRequest (localBaseUrl port) source runner)
    (stdout : IO.FS.Stream)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String))
    (responseBody : String)
    (response : IncrementalResponse responseBody) :
    IO (Except LocalApiErrorRetryError
      (Sigma fun successBody : String =>
        ApiErrorRetryResult source runner errorBody successBody)) := do
  let serverExit ← child.wait
  let serverStderr ← IO.ofExcept stderrTask.get
  let reportLine ← stdout.getLine
  match parseReport reportLine with
  | none => pure (.error (.report reportLine))
  | some (requests, validRequests) =>
      if hCounts : requests = 2 ∧ validRequests = 2 then
        match hOutcome : validateTerminalOutcome responseBody with
        | .error error => pure (.error (.secondOutcome error))
        | .ok outcome =>
            let processed : ProcessedOutcome responseBody := {
              response
              outcome
              outcome_exact := hOutcome
            }
            match hDispatch : dispatchOutcome runner outcome [] (by simp) (by simp) with
            | .error error => pure (.error (.secondDispatch error))
            | .ok dispatch =>
                if hExit : serverExit = 0 then
                  pure (.ok ⟨responseBody, {
                    firstStatus
                    firstValidated
                    firstTransportError := .httpStatus firstStatus errorBody
                    first_status_eq
                    first_transport_error_eq := rfl
                    accepted := {
                      port
                      prepared
                      response
                      processed
                      dispatch
                      dispatch_eq := hDispatch
                      requests
                      validRequests
                      serverExit
                      serverStderr
                      server_exit_eq := hExit
                    }
                    attempts := 2
                    attempts_eq := rfl
                    requests_eq := hCounts.1
                    valid_requests_eq := hCounts.2
                  }⟩)
                else
                  pure (.error (.server serverExit serverStderr))
      else
        pure (.error (.counts requests validRequests))

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxReads : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalApiErrorRetryError
      (Sigma fun errorBody : String => Sigma fun successBody : String =>
        ApiErrorRetryResult source runner errorBody successBody)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        match prepare (localBaseUrl port) source runner key with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.request error))
        | .ok prepared =>
            match ← executeSseIncremental maxReads (curlProcess {}) prepared.plan.request
                (fun _ _ => pure ()) with
            | .ok ⟨responseBody, _response⟩ =>
                stopServer child stderrTask
                pure (.error (.firstSuccess responseBody))
            | .error (.httpStatus firstStatus firstBody) =>
                match validateApiError firstBody with
                | .error error =>
                    stopServer child stderrTask
                    pure (.error (.firstEnvelope error))
                | .ok firstValidated =>
                    if hStatus : firstStatus = 429 then
                      let secondRequest := prepared.plan.request
                      match ← executeSseIncremental maxReads (curlProcess {}) secondRequest
                          (fun _ _ => pure ()) with
                      | .error error =>
                          stopServer child stderrTask
                          pure (.error (.secondTransport error))
                      | .ok ⟨responseBody, response⟩ =>
                          match ← finishAccepted port firstStatus hStatus firstValidated prepared
                              stdout child stderrTask responseBody response with
                          | .error error => pure (.error error)
                          | .ok ⟨successBody, result⟩ =>
                              pure (.ok ⟨firstBody, ⟨successBody, result⟩⟩)
                    else
                      stopServer child stderrTask
                      pure (.error (.firstStatus firstStatus))
            | .error error =>
                stopServer child stderrTask
                pure (.error (.firstTransport error))
  catch error =>
    stopServer child stderrTask
    pure (.error (.io (toString error)))

def runWithKey
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (errorBody : String)
    (successBody : String)
    (maxReads : Nat := 64) :
    IO (Except LocalApiErrorRetryError
      (Sigma fun firstBody : String => Sigma fun finalBody : String =>
        ApiErrorRetryResult source runner firstBody finalBody)) := do
  if errorBody.isEmpty || successBody.isEmpty then
    pure (.error .emptyBody)
  else
    try
      let child ← IO.Process.spawn {
        cmd := "python3"
        args := serverArgs errorBody successBody
        stdin := serverStdio.stdin
        stdout := serverStdio.stdout
        stderr := serverStdio.stderr
      }
      let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
      runChild source runner key maxReads child stderrTask
    catch error =>
      pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner := DeepSeekHarnessLocalSseOutcome.Example.runner

def errorBody : String := DeepSeekApiErrorEnvelope.exampleBody

def successBody : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except LocalApiErrorRetryError
    (Sigma fun firstBody : String => Sigma fun finalBody : String =>
      ApiErrorRetryResult DeepSeekHarness.counterRequestSource runner firstBody finalBody)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" }
    errorBody successBody 64

end Example

end Cordis.DeepSeekHarnessLocalSseApiErrorRetry
