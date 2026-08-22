import Cordis.DeepSeekCurlBytePrefixProviderAssemblyTool
import Cordis.DeepSeekHarnessLocalSse

/-!
# Loopback HTTP/SSE byte-framed provider/tool round

This module drives the byte-framed provider assembly adapter through a real one-shot loopback
HTTP/SSE server and the real curl executable.  The server validates the typed streaming request;
curl stdout is consumed as one-byte chunks, and completion reaches provider assembly, dependent
tool execution, and certified session append.

The result is local process/HTTP evidence only.  It does not establish remote reachability, TLS or
credential authenticity, provider obedience, backpressure, reconnects, arbitrary cleanup, or
equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseBytePrefixProviderAssemblyTool

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefixProviderAssemblyTool
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental

structure PreparedRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedRequest

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRequest

inductive LocalByteProviderAssemblyError where
  | request (error : RequestError)
  | round (error : BytePrefixToolRoundError)
  | pending
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq

structure LocalByteProviderAssemblyResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (source : RequestSource)
    (before : Model)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedRequest (localBaseUrl port) source runner
  body : String
  round : CompletedByteToolPrefix LinePolicy.never cfg before
  body_eq : round.observed.state.typed.body = body
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalByteProviderAssemblyResult

theorem streaming_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalByteProviderAssemblyResult cfg source before runner) :
    result.prepared.plan.source.stream = true :=
  result.prepared.streaming_mode

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalByteProviderAssemblyResult cfg source before runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

theorem provider_body_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {source : RequestSource} {before : Model} {runner : ConversationRunner}
    (result : LocalByteProviderAssemblyResult cfg source before runner) :
    result.round.provider.body = result.body := by
  calc
    result.round.provider.body = result.round.observed.state.typed.body :=
      result.round.body_eq
    _ = result.body := result.body_eq

end LocalByteProviderAssemblyResult

private def providerSseServerScript : String :=
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

private def serverArgs : Array String :=
  #[
    ("-u" : String),
    "-c",
    providerSseServerScript,
    DeepSeekProviderStreamAssembly.counterBody
  ]

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
    Except RequestError (PreparedRequest baseUrl source runner) :=
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
    IO (Except LocalByteProviderAssemblyError
      (LocalByteProviderAssemblyResult cfg source before runner)) := do
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
            let curlConfig := curlProcess { extraArgs := #["--no-buffer"] }
            match ← executeWithTimeout LinePolicy.never 4096 1 5000 curlConfig
                prepared.plan.request cfg before with
            | .error error =>
                stopServer child stderrTask
                pure (.error (.round error))
            | .ok (.pending _) =>
                stopServer child stderrTask
                pure (.error .pending)
            | .ok (.completed round) =>
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
                        body := round.observed.state.typed.body
                        round
                        body_eq := rfl
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
    IO (Except LocalByteProviderAssemblyError
      (LocalByteProviderAssemblyResult cfg source before runner)) := do
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

def runner : ConversationRunner := ConversationRunner.empty 1

def run : IO (Except LocalByteProviderAssemblyError
    (LocalByteProviderAssemblyResult Cordis.Harness.counterConfig
      DeepSeekHarness.counterRequestSource 2 runner)) :=
  runWithKey DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 2 runner
    { value := "fixture-key" }

def summary (result : LocalByteProviderAssemblyResult Cordis.Harness.counterConfig
    DeepSeekHarness.counterRequestSource 2 runner) : Bool :=
  result.requests == 1 &&
    result.validRequests == 1 &&
    result.body == DeepSeekProviderStreamAssembly.counterBody &&
    result.round.observed.state.typed.line == 8 &&
    result.round.provider.frames.length == 4 &&
    result.round.provider.raw.length == 6 &&
    result.round.certificate.result.blocks == [
      .toolCall "counter-call-0" "counter_increment" "[3,10]" ] &&
    result.round.execution.after == 5 &&
    result.round.execution.executions.length == 1

def summaryIO : IO Bool := do
  match ← run with
  | .error _ => pure false
  | .ok result => pure (summary result)

end Example

end Cordis.DeepSeekHarnessLocalSseBytePrefixProviderAssemblyTool
