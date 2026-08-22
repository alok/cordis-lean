import Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
import Cordis.DeepSeekSchemaStreamErrors
import Cordis.DeepSeekCurlTransport

/-!
# Current-event file restore into loopback recoverable schema SSE

This module composes the supported current-Harness event archive with the recoverable
heterogeneous schema stream.  A temporary-file restore supplies the initial runner; a real
loopback HTTP/SSE server then emits a two-tool body whose weather and clock providers both fail,
followed by a terminal text body.  The typed continuation appends two `isError` tool results and
then the terminal assistant, retaining the file/session evidence and exact final endpoint.

The fixture is deliberately local and finite.  It does not claim provider obedience, credential
authenticity, durable storage, blocked-read cancellation, reconnects, external effects, or
deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventFileLocalSseSchemaErrors

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSchemaStreamErrors
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

variable {Model Capability : Type}
variable {cfg : GenericHarness.Config Model Capability}

abbrev SourceBytes : ByteArray :=
  Cordis.DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes

abbrev FileRestored :=
  Cordis.DeepSeekHarnessEventFileStreamRetryCancellation.FileRestored

abbrev FileRunner (file : FileRestored) : ConversationRunner :=
  file.restored.restored.restored.runner

abbrev FailureRegistry
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool) :
    SchemaToolRegistry DeepSeekSchemaStreamErrors.Example.dualFailureConfig :=
  DeepSeekSchemaStreamErrors.Example.dualFailureRegistryEntries
    weatherCertificate clockCertificate

abbrev FailureSource
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool) :
    RegistryRequestSource (FailureRegistry weatherCertificate clockCertificate) :=
  DeepSeekSchemaStreamErrors.Example.dualFailureRequestSource
    weatherCertificate clockCertificate

abbrev Key : ApiKey := { value := "fixture-key" }

def localBaseUrl (port : Nat) : String :=
  "http://127.0.0.1:" ++ toString port

def parsePort (line : String) : Option Nat :=
  line.trimAscii.toString.toNat?

def parseReport (line : String) : Option (Nat × Nat) :=
  match line.trimAscii.toString.splitOn ":" with
  | ["requests", requests, "valid", valid] =>
      match requests.toNat?, valid.toNat? with
      | some requests, some valid => some (requests, valid)
      | _, _ => none
  | _ => none

private def serverScript : String :=
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
  "      tools=request.get('tools',[])\n" ++
  "      names=[tool.get('function',{}).get('name') for tool in tools]\n" ++
  "      good=self.path=='/chat/completions' and self.command=='POST' and " ++
  "self.headers.get('Authorization')=='Bearer fixture-key' and " ++
  "request.get('model')=='deepseek-reasoner' and request.get('stream') is True and " ++
  "names==['get_weather','get_time'] and request.get('tool_choice')=='auto' and " ++
  "request.get('messages')\n" ++
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
  #[("-u" : String), "-c", serverScript,
    DeepSeekSchemaStreamConversation.Example.dualToolStreamBody,
    DeepSeekRichStream.exampleTextStreamBody, toString expected]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

inductive LocalFailureError where
  | port (line : String)
  | report (line : String)
  | conversation (error : SchemaStreamRecoverableConversationError)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure LocalFailureResult
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (runner : ConversationRunner) where
  port : Nat
  outcome : Except SchemaStreamRecoverableConversationError
    (SchemaStreamRecoverableRunResult registry)
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalFailureResult

theorem server_exited_successfully
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {runner : ConversationRunner}
    (result : LocalFailureResult request runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

theorem server_requests_are_valid
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {runner : ConversationRunner}
    {expected : Nat}
    (result : LocalFailureResult request runner)
    (requests_eq : result.requests = expected)
    (valid_eq : result.validRequests = expected) :
    result.requests = result.validRequests := by
  rw [requests_eq, valid_eq]

end LocalFailureResult

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
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalFailureError (LocalFailureResult request runner)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        let config : ProcessConfig := curlProcess { extraArgs := #["--no-buffer"] }
        match ← runSchemaStreamRecoverable 2 config (localBaseUrl port) Key request []
            (by simp) (by simp) before runner with
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
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except LocalFailureError (LocalFailureResult request runner)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs 2
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild request before runner child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

structure FileFailureRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool) where
  file : FileRestored
  loopback : LocalFailureResult
    (FailureSource weatherCertificate clockCertificate) (FileRunner file)
  outcome : SchemaStreamRecoverableRunResult
    (FailureRegistry weatherCertificate clockCertificate)
  outcome_eq : loopback.outcome = .ok outcome

def runFixture : IO (Except Unit
    (Sigma fun weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool =>
      Sigma fun clockCertificate :
          ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool =>
        FileFailureRun weatherCertificate clockCertificate)) := do
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => pure (.error ())
  | .ok weatherCertificate =>
      match DeepSeekSchemaRegistry.Example.clockToolCertificate with
      | .error _ => pure (.error ())
      | .ok clockCertificate =>
          match ← restoreFile with
          | .error _ => pure (.error ())
          | .ok file =>
              let request := FailureSource weatherCertificate clockCertificate
              match ← runWithKey request 0 (FileRunner file) with
              | .error _ => pure (.error ())
              | .ok loopback =>
                  match outcome_eq : loopback.outcome with
                  | .error _ => pure (.error ())
                  | .ok outcome =>
                      pure (.ok ⟨weatherCertificate, ⟨clockCertificate,
                        { file, loopback, outcome, outcome_eq }⟩⟩)

theorem file_bytes_eq_source
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate) :
    run.file.bytes = SourceBytes :=
  run.file.bytes_eq_source

theorem restored_session_eq_event_archive
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate) :
    (FileRunner run.file).session =
      run.file.restored.restored.validated.validated.final.session :=
  RestoredTextRunner.session_eq run.file.restored.restored

theorem server_exited_successfully
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate) :
    run.loopback.serverExit = 0 :=
  run.loopback.server_exit_eq

theorem server_requests_match
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate)
    {expected : Nat}
    (requests_eq : run.loopback.requests = expected)
    (valid_eq : run.loopback.validRequests = expected) :
    run.loopback.requests = run.loopback.validRequests :=
  LocalFailureResult.server_requests_are_valid run.loopback requests_eq valid_eq

theorem successful_outcome
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate) :
    run.loopback.outcome = .ok run.outcome :=
  run.outcome_eq

def firstAttemptCount
    {registry : SchemaToolRegistry cfg} :
    List (SchemaStreamRecoverableRoundWitness registry) → Nat
  | [] => 0
  | round :: _ => round.result.batch.attempts.length

def firstFailureMessages
    {registry : SchemaToolRegistry cfg} :
    List (SchemaStreamRecoverableRoundWitness registry) → List String
  | [] => []
  | round :: _ => round.result.batch.attempts.map fun attempt =>
      match attempt with
      | .succeeded _ => "success"
      | .providerFailed failed => failed.message

def firstAllProviderFailed
    {registry : SchemaToolRegistry cfg} :
    List (SchemaStreamRecoverableRoundWitness registry) → Bool
  | [] => false
  | round :: _ => round.result.batch.attempts.all fun attempt =>
      match attempt with
      | .succeeded _ => false
      | .providerFailed _ => true

def stopCompleted
    {registry : SchemaToolRegistry cfg} :
    SchemaStreamRecoverableStop registry → Bool
  | .completed .. => true
  | .fuelExhausted => false

structure Summary where
  sourceBytes : Nat
  readBytes : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  requests : Nat
  validRequests : Nat
  rounds : Nat
  firstAttempts : Nat
  firstFailureMessages : List String
  firstAllProviderFailed : Bool
  finalModel : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def summaryForRun
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition DeepSeekSchemaRegistry.Example.clockTool}
    (run : FileFailureRun weatherCertificate clockCertificate) : Summary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := run.file.bytes.size
    initialNextSeq := (FileRunner run.file).session.nextSeq
    finalNextSeq := run.outcome.runner.session.nextSeq
    requests := run.loopback.requests
    validRequests := run.loopback.validRequests
    rounds := run.outcome.rounds.length
    firstAttempts := firstAttemptCount run.outcome.rounds
    firstFailureMessages := firstFailureMessages run.outcome.rounds
    firstAllProviderFailed := firstAllProviderFailed run.outcome.rounds
    finalModel := run.outcome.finalModel
    completed := stopCompleted run.outcome.stop
  }

def expectedSummary : Summary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := SourceBytes.size
    initialNextSeq := 8
    finalNextSeq := 12
    requests := 2
    validRequests := 2
    rounds := 2
    firstAttempts := 2
    firstFailureMessages := ["weather unavailable", "clock unavailable"]
    firstAllProviderFailed := true
    finalModel := 0
    completed := true
  }

def summaryMatches (value : Summary) : Bool := value == expectedSummary

def runSummary : IO (Except Unit Summary) := do
  match ← runFixture with
  | .error _ => pure (.error ())
  | .ok ⟨_, ⟨_, run⟩⟩ => pure (.ok (summaryForRun run))

end Cordis.DeepSeekHarnessEventFileLocalSseSchemaErrors
