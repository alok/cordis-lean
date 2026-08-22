import Cordis.DeepSeekCurlIncremental
import Cordis.DeepSeekHarness
import Cordis.DeepSeekStreamHarness

/-!
# Credential-safe local HTTP SSE round-trip for the typed DeepSeek Harness

`DeepSeekHarnessLocalHttp` proves a complete non-streaming curl round-trip.  This module closes
the next delivery seam: a one-shot loopback HTTP server emits an actual SSE body in complete line
chunks, the real curl executable carries a typed `stream: true` request, and the incremental
reader retains the delivered lines together with the reconstructed body and strict wire proof.

The successful result then runs the existing text-stream finisher and appends the certified
assistant to the indexed conversation runner.  The fixture validates method, route,
authorization, model, and stream mode before writing the body.  This is local process/HTTP
evidence only: it does not establish remote reachability, TLS, credential validity, provider
authenticity, backpressure, blocked-read interruption, reconnects, arbitrary cleanup, or deployed
Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSse

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

def localBaseUrl (port : Nat) : String :=
  "http://127.0.0.1:" ++ toString port

def sseServerScript : String :=
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
  "    if good:\n" ++
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
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

def parsePort (line : String) : Option Nat :=
  line.trimAscii.toString.toNat?

def parseReport (line : String) : Option (Nat × Nat) :=
  match line.trimAscii.toString.splitOn ":" with
  | ["requests", requests, "valid", valid] =>
      match requests.toNat?, valid.toNat? with
      | some requests, some valid => some (requests, valid)
      | _, _ => none
  | _ => none

structure PreparedStreamingRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedStreamingRequest

theorem build_exact
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl source runner) :
    buildTypedStreamingRequestPlan baseUrl prepared.key source runner.session = .ok prepared.plan :=
  prepared.build_eq

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedStreamingRequest

inductive LocalSseError where
  | emptyBody
  | request (error : RequestError)
  | stream (error : IncrementalError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalSseResult
    (source : RequestSource)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedStreamingRequest (localBaseUrl port) source runner
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

namespace LocalSseResult

theorem streaming_mode
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseResult source runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem append_endpoint
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseResult source runner) :
    result.after =
      ConversationRunner.appendFinished runner result.finished [] (by simp) (by simp) :=
  result.append_eq

theorem nextSeq
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseResult source runner) :
    result.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [result.append_eq]
  exact ConversationRunner.appendFinished_nextSeq runner result.finished [] (by simp) (by simp)

theorem server_exited_successfully
    {source : RequestSource} {runner : ConversationRunner}
    (result : LocalSseResult source runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSseResult

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
    Except RequestError (PreparedStreamingRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxReads : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseError (LocalSseResult source runner)) := do
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
            | .error error =>
                stopServer child stderrTask
                pure (.error (.stream error))
            | .ok ⟨responseBody, response⟩ =>
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

def runWithKey
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (maxReads : Nat := 64) :
    IO (Except LocalSseError (LocalSseResult source runner)) := do
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

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except LocalSseError
    (LocalSseResult DeepSeekHarness.counterRequestSource runner)) :=
  runWithKey DeepSeekHarness.counterRequestSource runner { value := "fixture-key" } body 64

structure Summary where
  requests : Nat
  validRequests : Nat
  deliveredLines : Nat
  bodyLength : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def expectedSummary : Summary := {
  requests := 1
  validRequests := 1
  deliveredLines := 7
  bodyLength := body.length
  initialNextSeq := 1
  finalNextSeq := 2
  completed := true
}

def summarize
    (result : LocalSseResult DeepSeekHarness.counterRequestSource runner) : Summary := {
  requests := result.requests
  validRequests := result.validRequests
  deliveredLines := result.response.lines.length
  bodyLength := result.body.length
  initialNextSeq := runner.session.nextSeq
  finalNextSeq := result.after.session.nextSeq
  completed := result.response.wire.frames.any (fun frame => match frame with
    | .done => true
    | .data _ => false)
}

theorem expectedSummary_complete : expectedSummary.completed = true := rfl

end Example

end Cordis.DeepSeekHarnessLocalSse
