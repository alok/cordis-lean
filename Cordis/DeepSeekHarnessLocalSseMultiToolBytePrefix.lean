import Cordis.DeepSeekHarnessLocalSseMultiToolPrefix
import Cordis.DeepSeekStreamHarnessBytePrefix

/-!
# Loopback HTTP SSE multi-tool byte-prefix continuation

This module drives the process-byte prefix continuation through a real loopback HTTP/SSE server.
The server validates the typed streaming request; curl stdout is consumed as bounded byte chunks,
complete lines feed the byte-prefix state, and a completed response reaches the dependent
multi-tool runner. A read-budget stop retains the raw byte prefix and never fabricates execution.

The result is local process/HTTP evidence only. It does not establish byte-level backpressure,
blocked-read interruption, reconnect policy, provider-complete assembly, credential or TLS
authenticity, arbitrary process cleanup, or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseMultiToolBytePrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseMultiToolPrefix
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessBytePrefix

inductive LocalSseMultiToolBytePrefixError where
  | request (error : RequestError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalSseMultiToolBytePrefixResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (source : RequestSource)
    (before : Model)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedMultiToolPrefixRequest (localBaseUrl port) source runner
  outcome : Except BytePrefixConversationError
    (Sigma fun body : String => BytePrefixConversationRoundResult cfg before body)
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalSseMultiToolBytePrefixResult

theorem streaming_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolBytePrefixResult cfg source before runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalSseMultiToolBytePrefixResult cfg source before runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSseMultiToolBytePrefixResult

private def bytePrefixServerScript : String :=
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
  #[("-u" : String), "-c", bytePrefixServerScript, counterMultiToolStreamBody]

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
    (maxReads chunkSize : Nat)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseMultiToolBytePrefixError
      (LocalSseMultiToolBytePrefixResult cfg source before runner)) := do
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
            let outcome ← executeConversationMultiBytePrefixRound maxReads chunkSize
              (curlProcess { extraArgs := #["--no-buffer"] }) baseUrl key source cfg before runner
              [] (by simp) (by simp)
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

def runWithReads
    {Model Capability : Type}
    (maxReads chunkSize : Nat)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalSseMultiToolBytePrefixError
      (LocalSseMultiToolBytePrefixResult cfg source before runner)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild maxReads chunkSize source cfg before runner key child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def completeRun : IO (Except LocalSseMultiToolBytePrefixError
    (LocalSseMultiToolBytePrefixResult Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithReads 4096 1 DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig
    0 runner { value := "fixture-key" }

def exhaustedRun : IO (Except LocalSseMultiToolBytePrefixError
    (LocalSseMultiToolBytePrefixResult Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 0 runner)) :=
  runWithReads 1 1 DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig
    0 runner { value := "fixture-key" }

end Example

end Cordis.DeepSeekHarnessLocalSseMultiToolBytePrefix
