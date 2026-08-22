import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekSchemaConversationLoop

/-!
# Loopback HTTP/curl witness for the heterogeneous schema conversation

This module crosses the existing complete-body schema conversation with the actual local process
boundary.  A one-shot Python HTTP server validates the route, method, authorization, model,
complete-response mode, and two declared tools; the existing curl adapter sends two requests and
returns a tool-call body followed by a terminal body.  The dependent conversation result retains
the prepared request, heterogeneous execution round, terminal witness, final model, request
counts, and server-exit evidence together.

The fixture is deliberately local evidence.  It does not establish remote reachability, TLS or
credential authenticity, provider obedience, shell/process trust, retry or cancellation semantics,
persistence, external side effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaLocalHttp

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaConversationLoop
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekToolSchema

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
  "responses=sys.argv[1:]\n" ++
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
  "request.get('model')=='deepseek-reasoner' and request.get('stream') is False and " ++
  "names==['get_weather','get_time'] and request.get('tool_choice')=='auto' and " ++
  "request.get('messages')\n" ++
  "    except Exception:\n" ++
  "      good=False\n" ++
  "    if good and H.count < len(responses):\n" ++
  "      body=responses[H.count].encode()\n" ++
  "      H.count += 1\n" ++
  "      H.valid += 1\n" ++
  "      status=200\n" ++
  "    else:\n" ++
  "      body=b'{\"error\":\"fixture request mismatch\"}'\n" ++
  "      status=400\n" ++
  "    self.send_response(status)\n" ++
  "    self.send_header('Content-Type','application/json')\n" ++
  "    self.send_header('Content-Length',str(len(body)))\n" ++
  "    self.end_headers()\n" ++
  "    self.wfile.write(body)\n" ++
  "    self.wfile.flush()\n" ++
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "for _ in responses: server.handle_request()\n" ++
  "print('requests:'+str(H.count)+':valid:'+str(H.valid),flush=True)\n"

private def serverArgs (responses : List String) : Array String :=
  #[("-u" : String), "-c", serverScript] ++ responses.toArray

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

inductive LocalSchemaHttpError where
  | emptyResponses
  | port (line : String)
  | request (error : RequestError)
  | conversation (error : SchemaConversationError)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure PreparedRequest
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (baseUrl : String)
    (key : ApiKey)
    (runner : ConversationRunner) where
  plan : TypedRequestPlan .complete
  build_eq : buildTypedCompleteRequestPlan baseUrl key request.source runner.session = .ok plan

namespace PreparedRequest

theorem complete_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner}
    (prepared : PreparedRequest request baseUrl key runner) :
    prepared.plan.source.stream = false :=
  prepared.plan.complete_source_stream

theorem body_eq_source
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner}
    (prepared : PreparedRequest request baseUrl key runner) :
    prepared.plan.request.body =
      Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRequest

structure LocalSchemaHttpResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (runner : ConversationRunner)
    (before : Model)
    (key : ApiKey) where
  port : Nat
  prepared : PreparedRequest request (localBaseUrl port) key runner
  result : SchemaConversationRunResult registry
  requests : Nat
  validRequests : Nat
  serverExit : UInt32
  serverStderr : String
  server_exit_eq : serverExit = 0

namespace LocalSchemaHttpResult

theorem complete_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {runner : ConversationRunner} {before : Model} {key : ApiKey}
    (result : LocalSchemaHttpResult request runner before key) :
    result.prepared.plan.source.stream = false :=
  result.prepared.complete_mode

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {runner : ConversationRunner} {before : Model} {key : ApiKey}
    (result : LocalSchemaHttpResult request runner before key) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalSchemaHttpResult

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
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (baseUrl : String)
    (key : ApiKey)
    (runner : ConversationRunner) :
    Except RequestError (PreparedRequest request baseUrl key runner) :=
  match built : buildTypedCompleteRequestPlan baseUrl key request.source runner.session with
  | .error error => .error error
  | .ok plan =>
      .ok {
        plan
        build_eq := built
      }

private def runChild
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (fuel : Nat)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSchemaHttpError
      (LocalSchemaHttpResult request runner before key)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        let baseUrl := localBaseUrl port
        match prepare request baseUrl key runner with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.request error))
        | .ok prepared =>
            let transport := curlTransport {}
            match ← runSchemaConversation fuel transport baseUrl key request []
                (by simp) (by simp) before runner with
            | .error error =>
                stopServer child stderrTask
                pure (.error (.conversation error))
            | .ok result =>
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
                        result
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

private def runNonempty
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (fuel : Nat)
    (responses : List String)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalSchemaHttpError
      (LocalSchemaHttpResult request runner before key)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs responses
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild request fuel before runner key child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

def runWithKey
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (fuel : Nat)
    (responses : List String)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalSchemaHttpError
      (LocalSchemaHttpResult request runner before key)) := do
  if responses.isEmpty then
    pure (.error .emptyResponses)
  else
    runNonempty request fuel responses before runner key

/-! ## Executable heterogeneous two-round witness -/

namespace Example

open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry.Example

def responses : List String := [
  dualResponseBody,
  DeepSeekHarness.counterFinalResponseBody
]

def run
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except LocalSchemaHttpError
      (LocalSchemaHttpResult
        (dualRequestSource weatherCertificate clockCertificate)
        DeepSeekSchemaHarness.Example.counterRunner 0 { value := "fixture-key" })) :=
  runWithKey (dualRequestSource weatherCertificate clockCertificate) 2 responses 0
    DeepSeekSchemaHarness.Example.counterRunner { value := "fixture-key" }

structure Summary where
  requests : Nat
  validRequests : Nat
  toolRounds : Nat
  finalNextSeq : Nat
  finalModel : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def expectedSummary : Summary := {
  requests := 2
  validRequests := 2
  toolRounds := 1
  finalNextSeq := 4
  finalModel := 0
  completed := true
}

def summarize
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition clockTool}
    (result : LocalSchemaHttpResult
      (dualRequestSource weatherCertificate clockCertificate)
      DeepSeekSchemaHarness.Example.counterRunner 0 { value := "fixture-key" }) :
    Summary := {
      requests := result.requests
      validRequests := result.validRequests
      toolRounds := result.result.rounds.length
      finalNextSeq := result.result.runner.session.nextSeq
      finalModel := result.result.finalModel
      completed := match result.result.stop with
        | .completed _ => true
        | .fuelExhausted _ _ => false
    }

theorem expectedSummary_complete : expectedSummary.completed = true := rfl

end Example

end Cordis.DeepSeekSchemaLocalHttp
