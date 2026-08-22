import Cordis.DeepSeekHarnessLocalSse
import Cordis.DeepSeekStreamHarnessPrefix

/-!
# Loopback HTTP SSE multi-tool prefix continuation

This module lifts the line-oriented proof-carrying prefix runner to a real loopback HTTP/SSE
server.  Complete lines are fed through `PrefixState` before the next curl read; completion then
uses the dependent multi-tool conversation runner, while fuel exhaustion and line cancellation
retain the exact typed prefix and never fabricate tool execution.

The result is local process/HTTP evidence only.  It does not establish byte framing, backpressure,
fairness, arbitrary cleanup, provider-complete assembly, reconnect policy, credential or TLS
authenticity, or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseMultiToolPrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessPrefix
open Cordis.DeepSeekStreamIncremental

structure PreparedMultiToolPrefixRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedMultiToolPrefixRequest

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedMultiToolPrefixRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedMultiToolPrefixRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedMultiToolPrefixRequest

inductive LocalSseMultiToolPrefixError where
  | request (error : RequestError)
  | round (error : PrefixStreamConversationError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalSseMultiToolPrefixResult
    {Model Capability : Type}
    (policy : LinePolicy)
    (cfg : GenericHarness.Config Model Capability)
    (source : RequestSource)
    (before : Model)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedMultiToolPrefixRequest (localBaseUrl port) source runner
  outcome : PrefixStreamRoundOutcome policy cfg before
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalSseMultiToolPrefixResult

theorem streaming_mode
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolPrefixResult policy cfg source before runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem server_exited_successfully
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolPrefixResult policy cfg source before runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSseMultiToolPrefixResult

private def prefixServerScript : String :=
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
  "    try:\n" ++
  "      for line in payload.splitlines(True):\n" ++
  "        self.wfile.write(line)\n" ++
  "        self.wfile.flush()\n" ++
  "    except BrokenPipeError:\n" ++
  "      pass\n" ++
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

private def serverArgs : Array String :=
  #[("-u" : String), "-c", prefixServerScript, counterMultiToolStreamBody]

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
    Except RequestError (PreparedMultiToolPrefixRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private def runChild
    {Model Capability : Type}
    (policy : LinePolicy)
    (maxReads : Nat)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseMultiToolPrefixError
      (LocalSseMultiToolPrefixResult policy cfg source before runner)) := do
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
            match ← executeConversationMultiStreamPrefixRound policy maxReads
                (curlProcess { extraArgs := #["--no-buffer"] }) baseUrl key source cfg before runner
                [] (by simp) (by simp) with
            | .error error =>
                stopServer child stderrTask
                pure (.error (.round error))
            | .ok outcome =>
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
                        outcome
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

def runWithPolicy
    {Model Capability : Type}
    (policy : LinePolicy)
    (maxReads : Nat)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalSseMultiToolPrefixError
      (LocalSseMultiToolPrefixResult policy cfg source before runner)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild policy maxReads source cfg before runner key child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def completeRun : IO (Except LocalSseMultiToolPrefixError
    (LocalSseMultiToolPrefixResult LinePolicy.never Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithPolicy LinePolicy.never 64 DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig
    0 runner { value := "fixture-key" }

def cancelledRun : IO (Except LocalSseMultiToolPrefixError
    (LocalSseMultiToolPrefixResult (LinePolicy.atLine 1 "line:user") Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithPolicy (LinePolicy.atLine 1 "line:user") 64 DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig 0 runner { value := "fixture-key" }

def exhaustedRun : IO (Except LocalSseMultiToolPrefixError
    (LocalSseMultiToolPrefixResult LinePolicy.never Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithPolicy LinePolicy.never 1 DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig
    0 runner { value := "fixture-key" }

end Example

end Cordis.DeepSeekHarnessLocalSseMultiToolPrefix
