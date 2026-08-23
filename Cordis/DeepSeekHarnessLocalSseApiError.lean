import Cordis.DeepSeekApiErrorEnvelope
import Cordis.DeepSeekHarnessLocalSseOutcome

/-!
# Loopback HTTP API-error envelopes into the typed harness boundary

This module exercises a real local Python HTTP server and curl process on the non-success
response path. The server validates the typed streaming request, returns an OpenAI-compatible
JSON error envelope with status 429, and then exits. The result retains the request certificate,
the exact status/body `IncrementalError.httpStatus` branch, the dependent parsed API error, the
request report, and process-exit evidence.

The fixture is deliberately local evidence only. It does not establish provider authenticity,
retry safety, credential validity, TLS, deployed Harness equivalence, or any external side-effect
policy.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseApiError

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiErrorEnvelope
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseOutcome

def apiErrorServerScript : String :=
  "import http.server,json,sys\n" ++
  "body=sys.argv[1].encode()\n" ++
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
  "      payload=body\n" ++
  "      status=429\n" ++
  "    else:\n" ++
  "      payload=b'{\"error\":{\"message\":\"fixture request mismatch\"," ++
  "\"type\":\"invalid_request_error\",\"param\":null,\"code\":\"400\"}}'\n" ++
  "      status=400\n" ++
  "    self.send_response(status)\n" ++
  "    self.send_header('Content-Type','application/json')\n" ++
  "    self.send_header('Content-Length',str(len(payload)))\n" ++
  "    self.end_headers()\n" ++
  "    self.wfile.write(payload)\n" ++
  "    self.wfile.flush()\n" ++
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

inductive LocalApiErrorError where
  | request (error : RequestError)
  | transport (error : IncrementalError)
  | unexpectedSuccess (body : String)
  | unexpectedStatus (status : Nat)
  | counts (requests : Nat) (validRequests : Nat)
  | envelope (error : DeepSeekApiErrorEnvelope.ValidationError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure ApiErrorResult
    (source : RequestSource)
    (runner : ConversationRunner)
    (body : String) where
  port : Nat
  prepared : PreparedOutcomeRequest (localBaseUrl port) source runner
  status : Nat
  validated : ValidatedApiError body
  transportError : IncrementalError
  transport_error_eq : transportError = .httpStatus status body
  requests : Nat
  validRequests : Nat
  requests_eq : requests = 1
  valid_requests_eq : validRequests = 1
  serverExit : UInt32
  serverStderr : String
  status_eq : status = 429
  server_exit_eq : serverExit = 0

namespace ApiErrorResult

theorem streaming_mode
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem body_is_validated_api_error
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    Lean.Json.parse body = .ok result.validated.json :=
  result.validated.parsed

theorem decoded_api_error
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    decodeResponseJson result.validated.json = .error (.api result.validated.error) :=
  result.validated.decoded

theorem transport_error_is_http_status
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    result.transportError = .httpStatus result.status body :=
  result.transport_error_eq

theorem status_is_rate_limited
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    result.status = 429 :=
  result.status_eq

theorem requests_are_valid
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    result.requests = 1 ∧ result.validRequests = 1 :=
  ⟨result.requests_eq, result.valid_requests_eq⟩

theorem server_exited_successfully
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : ApiErrorResult source runner body) :
    result.serverExit = 0 :=
  result.server_exit_eq

end ApiErrorResult

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
  #[("-u" : String), "-c", apiErrorServerScript, body]

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

private def finishServer
    (port : Nat)
    {source : RequestSource}
    {runner : ConversationRunner}
    (stdout : IO.FS.Stream)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String))
    (status : Nat)
    (body : String)
    (prepared : PreparedOutcomeRequest (localBaseUrl port) source runner) :
    IO (Except LocalApiErrorError
      (Sigma fun errorBody : String => ApiErrorResult source runner errorBody)) := do
  let serverExit ← child.wait
  let serverStderr ← IO.ofExcept stderrTask.get
  let reportLine ← stdout.getLine
  match parseReport reportLine with
  | none => pure (.error (.report reportLine))
  | some (requests, validRequests) =>
      if hCounts : requests = 1 ∧ validRequests = 1 then
        match validateApiError body with
        | .error error => pure (.error (.envelope error))
        | .ok validated =>
            if hStatus : status = 429 then
              if hExit : serverExit = 0 then
                pure (.ok ⟨body, {
                  port
                  prepared
                  status
                  validated
                  transportError := .httpStatus status body
                  transport_error_eq := rfl
                  requests
                  validRequests
                  requests_eq := hCounts.1
                  valid_requests_eq := hCounts.2
                  serverExit
                  serverStderr
                  status_eq := hStatus
                  server_exit_eq := hExit
                }⟩)
              else
                pure (.error (.server serverExit serverStderr))
            else
              pure (.error (.unexpectedStatus status))
      else
        pure (.error (.counts requests validRequests))

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxReads : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalApiErrorError
      (Sigma fun responseBody : String => ApiErrorResult source runner responseBody)) := do
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
            match ← executeSseIncremental maxReads (curlProcess {}) prepared.plan.request
                (fun _ _ => pure ()) with
            | .ok ⟨responseBody, _response⟩ =>
                stopServer child stderrTask
                pure (.error (.unexpectedSuccess responseBody))
            | .error (.httpStatus status responseBody) =>
                match ← finishServer port stdout child stderrTask status responseBody
                    prepared with
                | .error error => pure (.error error)
                | .ok result => pure (.ok result)
            | .error error =>
                stopServer child stderrTask
                pure (.error (.transport error))
  catch error =>
    stopServer child stderrTask
    pure (.error (.io (toString error)))

def runWithKey
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (maxReads : Nat := 64) :
    IO (Except LocalApiErrorError
      (Sigma fun responseBody : String => ApiErrorResult source runner responseBody)) := do
  if body.isEmpty then
    pure (.error (.envelope DeepSeekApiErrorEnvelope.ValidationError.notApiError))
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

def runner : ConversationRunner := DeepSeekHarnessLocalSseOutcome.Example.runner

def body : String := DeepSeekApiErrorEnvelope.exampleBody

def run : IO (Except LocalApiErrorError
    (Sigma fun responseBody : String =>
      ApiErrorResult DeepSeekHarness.counterRequestSource runner responseBody)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } body 64

end Example

end Cordis.DeepSeekHarnessLocalSseApiError
