import Cordis.DeepSeekHarnessLocalSse

/-!
# Credential-safe loopback SSE retry

`DeepSeekHarnessLocalSse` proves one real loopback HTTP/SSE attempt.  This module composes a
bounded retry around that same process boundary: the fixture returns one validated transient HTTP
failure, the second request receives the real flushed SSE body, and only that accepted terminal
body is finished and appended to the dependent conversation runner.  The retry history retains
the typed incremental failure instead of collapsing it into a generic client error.

This is a local two-attempt reconnect witness.  It does not establish provider backoff,
idempotency of external tools, arbitrary reconnect policies, blocked-read cancellation,
backpressure, cleanup of arbitrary descendants, credential validity, TLS, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

def retryServerScript : String :=
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
  "    if good: H.valid += 1\n" ++
  "    if good and H.count == 1:\n" ++
  "      payload=b'busy\\n'\n" ++
  "      status=503\n" ++
  "      content='application/json'\n" ++
  "    elif good:\n" ++
  "      payload=body\n" ++
  "      status=200\n" ++
  "      content='text/event-stream'\n" ++
  "    else:\n" ++
  "      payload=b'{\"error\":\"fixture request mismatch\"}'\n" ++
  "      status=400\n" ++
  "      content='application/json'\n" ++
  "    self.send_response(status)\n" ++
  "    self.send_header('Content-Type',content)\n" ++
  "    self.send_header('Content-Length',str(len(payload)))\n" ++
  "    self.end_headers()\n" ++
  "    for line in payload.splitlines(True):\n" ++
  "      self.wfile.write(line)\n" ++
  "      self.wfile.flush()\n" ++
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "server.handle_request()\n" ++
  "server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

inductive LocalSseRetryError where
  | emptyBody
  | request (error : RequestError)
  | stream (error : IncrementalError)
  | retryExhausted (failures : List IncrementalError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalSseRetryResult
    (source : RequestSource)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedStreamingRequest (localBaseUrl port) source runner
  failures : List IncrementalError
  attempts : Nat
  attempts_eq : attempts = failures.length + 1
  body : String
  response : IncrementalResponse body
  finished : FinishedResponse body
  after : ConversationRunner
  append_eq : after = ConversationRunner.appendFinished runner finished [] (by simp) (by simp)
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalSseRetryResult

theorem retry_count
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseRetryResult source runner) :
    result.attempts = result.failures.length + 1 :=
  result.attempts_eq

theorem accepted_streaming
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseRetryResult source runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem append_endpoint
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseRetryResult source runner) :
    result.after =
      ConversationRunner.appendFinished runner result.finished [] (by simp) (by simp) :=
  result.append_eq

theorem nextSeq
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseRetryResult source runner) :
    result.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [result.append_eq]
  exact ConversationRunner.appendFinished_nextSeq runner result.finished [] (by simp) (by simp)

theorem server_exited_successfully
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseRetryResult source runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSseRetryResult

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
  #[("-u" : String), "-c", retryServerScript, body]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

private def retryable (error : IncrementalError) : Bool :=
  match error with
  | .httpStatus status _ => 500 ≤ status && status < 600
  | _ => false

private def prepare
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey) :
    Except RequestError (PreparedStreamingRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private def retryAttempts
    (remaining : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (failures : List IncrementalError) :
    IO (Except LocalSseRetryError
      (Sigma fun body : String => IncrementalResponse body × List IncrementalError)) := do
  match ← executeSseIncremental 64 config request (fun _ _ => pure ()) with
  | .ok ⟨body, response⟩ => pure (.ok ⟨body, (response, failures)⟩)
  | .error error =>
      if retryable error then
        match remaining with
        | 0 => pure (.error (.retryExhausted (failures ++ [error])))
        | remaining + 1 => retryAttempts remaining config request (failures ++ [error])
      else
        pure (.error (.stream error))

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxRetries : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseRetryError (LocalSseRetryResult source runner)) := do
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
            match ← retryAttempts maxRetries (curlProcess {}) prepared.plan.request [] with
            | .error error =>
                stopServer child stderrTask
                pure (.error error)
            | .ok ⟨responseBody, (response, failures)⟩ =>
                let serverExit ← child.wait
                let serverStderr ← IO.ofExcept stderrTask.get
                let reportLine ← stdout.getLine
                match parseReport reportLine with
                | none => pure (.error (.report reportLine))
                | some (requests, validRequests) =>
                    match finishText responseBody with
                    | .error error => pure (.error (.response error))
                    | .ok finished =>
                        if hExit : serverExit = 0 then
                          pure (.ok {
                            port
                            prepared
                            failures
                            attempts := failures.length + 1
                            attempts_eq := rfl
                            body := responseBody
                            response
                            finished
                            after := ConversationRunner.appendFinished runner finished [] (by simp)
                              (by simp)
                            append_eq := rfl
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

def runWithRetry
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (maxRetries : Nat := 1) :
    IO (Except LocalSseRetryError (LocalSseRetryResult source runner)) := do
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
      runChild source runner key maxRetries child stderrTask
    catch error =>
      pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except LocalSseRetryError
    (LocalSseRetryResult DeepSeekHarness.counterRequestSource runner)) :=
  runWithRetry DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } body 1

structure Summary where
  requests : Nat
  validRequests : Nat
  failedAttempts : Nat
  deliveredLines : Nat
  finalNextSeq : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def summarize
    (result : LocalSseRetryResult DeepSeekHarness.counterRequestSource runner) : Summary := {
  requests := result.requests
  validRequests := result.validRequests
  failedAttempts := result.failures.length
  deliveredLines := result.response.lines.length
  finalNextSeq := result.after.session.nextSeq
  completed := result.response.wire.frames.any (fun frame => match frame with
    | .done => true
    | .data _ => false)
}

def expectedSummary : Summary := {
  requests := 2
  validRequests := 2
  failedAttempts := 1
  deliveredLines := 7
  finalNextSeq := 2
  completed := true
}

theorem expectedSummary_complete : expectedSummary.completed = true := rfl

end Example

end Cordis.DeepSeekHarnessLocalSseRetry
