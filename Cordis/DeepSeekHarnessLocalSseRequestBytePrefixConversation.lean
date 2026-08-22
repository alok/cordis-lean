import Cordis.DeepSeekProcessScopedRequestBytePrefixConversation
import Cordis.DeepSeekHarnessLocalSse
import Cordis.DeepSeekSchemaStreamConversation

/-!
# Loopback request-indexed byte-prefix scoped conversation

This module closes the gap between the process-only request-indexed conversation and the
loopback HTTP fixtures.  One local Python server handles a bounded sequence of requests and
selects the SSE body by request index.  Each Lean round rebuilds the typed streaming request
from the current session, sends it through real curl, consumes stdout in bounded byte chunks,
and retains the exact request-indexed scoped/dependent/session witness.

The fixture is deliberately local and finite.  It proves method/route/auth/model/stream
validation, request-body evolution, arbitrary-byte ingress, strict SSE completion, scoped
approval, dependent execution, exact session append, and typed complete/prefix/fuel stops.  It
does not claim remote reachability, credential or executable authenticity, backpressure,
blocked-read interruption, reconnects, retries, persistence, external effects, or deployed
Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekProcessScopedRequestBytePrefixConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekScopedStreamToolRound
open Cordis.DeepSeekToolSchema
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.GenericHarness

private def loopbackServerScript : String :=
  "import http.server,json,sys\n" ++
  "bodies=[sys.argv[1].encode(),sys.argv[2].encode()]\n" ++
  "expected=int(sys.argv[3])\n" ++
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
  "    index=H.count\n" ++
  "    H.count += 1\n" ++
  "    if good and index < len(bodies):\n" ++
  "      H.valid += 1\n" ++
  "      payload=bodies[index]\n" ++
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
  "while H.count < expected:\n" ++
  "  server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

private def serverArgs (expected : Nat) : Array String :=
  #[("-u" : String), "-c", loopbackServerScript,
    dualToolStreamBody, DeepSeekRichStream.exampleTextStreamBody, toString expected]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

inductive LocalConversationError where
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | conversation (error : RequestByteConversationError)
  | io (message : String)

structure LocalConversationResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (key : ApiKey)
    (source : RequestSource)
    (before : Model)
    (session : Session.Session Session.noExtensions) where
  port : Nat
  outcome : Except RequestByteConversationError
    (ConversationResult registry approval (localBaseUrl port) key source)
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalConversationResult

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {key : ApiKey}
    {source : RequestSource}
    {before : Model}
    {session : Session.Session Session.noExtensions}
    (result : LocalConversationResult registry approval key source before session) :
    result.serverExit = 0 :=
  result.server_exit_eq

theorem server_requests_are_valid
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {key : ApiKey}
    {source : RequestSource}
    {before : Model}
    {session : Session.Session Session.noExtensions}
    {expected : Nat}
    (result : LocalConversationResult registry approval key source before session)
    (requests_eq : result.requests = expected)
    (valid_eq : result.validRequests = expected) :
    result.requests = result.validRequests := by
  rw [requests_eq, valid_eq]

end LocalConversationResult

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

private def runChild
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (key : ApiKey)
    (source : RequestSource)
    (before : Model)
    (session : Session.Session Session.noExtensions)
    (fuel maxReads chunkSize : Nat)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except (LocalConversationError)
      (LocalConversationResult registry approval key source before session)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        let baseUrl := localBaseUrl port
        let config : Nat → ProcessConfig := fun _ =>
          curlProcess { extraArgs := #["--no-buffer"] }
        match ← Cordis.DeepSeekProcessScopedRequestBytePrefixConversation.run registry approval
            baseUrl key source fuel maxReads chunkSize config before session with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.conversation error))
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
                    outcome := .ok outcome
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
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (key : ApiKey)
    (source : RequestSource)
    (before : Model)
    (session : Session.Session Session.noExtensions)
    (fuel expectedRequests maxReads chunkSize : Nat) :
    IO (Except LocalConversationError
      (LocalConversationResult registry approval key source before session)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs expectedRequests
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild registry approval key source before session fuel maxReads chunkSize child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

namespace Example

open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example

def key : ApiKey := { value := "fixture-key" }

def source : RequestSource where
  model := "deterministic-counter"
  system := some "Use the certified weather and clock tools."
  tools := [DeepSeekApi.exampleTool, clockTool]
  toolChoice := some .auto

def initialSession : Session.Session Session.noExtensions :=
  (Session.Session.empty Session.noExtensions).appendSurface .userMessage
    { content := "Read the weather and time." } [] (by simp) (by simp)

def runTwoSteps
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except LocalConversationError
      (LocalConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy key source 0
          initialSession)) :=
  runWithKey (scopedRegistry weatherCertificate clockCertificate) approvalPolicy key source 0
    initialSession 2 2 4096 1

def runPrefixFuel
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except LocalConversationError
      (LocalConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy key source 0
          initialSession)) :=
  runWithKey (scopedRegistry weatherCertificate clockCertificate) approvalPolicy key source 0
    initialSession 1 1 1 1

def twoStepSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runTwoSteps weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          match result.outcome with
          | .error _ => pure false
          | .ok outcome =>
              pure (result.requests == 2 && result.validRequests == 2 &&
                outcome.rounds.length == 2 && RoundWitness.allByteComplete outcome.rounds &&
                RoundWitness.firstTwoBodiesDistinct outcome.rounds &&
                RoundWitness.firstHasManyByteChunks outcome.rounds && outcome.finalModel == 0 &&
                outcome.session.messages.length == 5 && outcome.session.nextSeq == 5 &&
                !ConversationStop.isFuelExhausted outcome.stop &&
                !ConversationStop.isPrefixFuelExhausted outcome.stop)
  | _, _ => pure false

def prefixFuelSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runPrefixFuel weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          match result.outcome with
          | .error _ => pure false
          | .ok outcome =>
              pure (result.requests == 1 && result.validRequests == 1 &&
                ConversationStop.isPrefixFuelExhausted outcome.stop && outcome.rounds.isEmpty &&
                outcome.session.messages.length == 1 && outcome.session.nextSeq == 1)
  | _, _ => pure false

end Example

end Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation
