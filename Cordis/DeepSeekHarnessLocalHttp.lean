import Cordis.DeepSeekHarnessLiveProbe

/-!
# Credential-safe local HTTP round-trip for the typed DeepSeek Harness

`DeepSeekHarnessLiveProbe` already proves the request/conversation path with an injected
transport and exposes the configured curl adapter.  This module closes the next runtime seam:
it starts a one-shot loopback HTTP server, sends the real request through the real `curl`
executable, and retains a dependent result for the same bounded conversation.

The fixture server validates the request method, path, authorization header, JSON model, and
`stream: false` mode before returning the existing two-round counter responses.  Its port,
request count, validity count, exit code, stderr, prepared request, and conversation result are
retained together.  This is local process/network evidence only: it does not establish remote
reachability, credential validity, TLS, provider obedience, executable trust, backoff,
idempotency, cleanup of arbitrary descendants, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalHttp

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLiveProbe
open Cordis.DeepSeekSessionRunner

inductive LocalHttpError where
  | emptyResponses
  | port (line : String)
  | request (error : ProbeError)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

def localBaseUrl (port : Nat) : String :=
  "http://127.0.0.1:" ++ toString port

def serverScript : String :=
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
  "      good=self.path=='/chat/completions' and self.command=='POST' and " ++
  "self.headers.get('Authorization')=='Bearer fixture-key' and " ++
  "request.get('model')=='deterministic-counter' and request.get('stream') is False\n" ++
  "    except Exception:\n" ++
  "      good=False\n" ++
  "    if good:\n" ++
  "      body=responses[min(H.count,len(responses)-1)].encode()\n" ++
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
  "  def log_message(self,*args): pass\n" ++
  "server=http.server.HTTPServer(('127.0.0.1',0),H)\n" ++
  "print(server.server_port,flush=True)\n" ++
  "for _ in responses: server.handle_request()\n" ++
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

structure LocalProbeResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (runner : ConversationRunner) where
  port : Nat
  requests : Nat
  validRequests : Nat
  config : ProbeConfig
  prepared : PreparedRequest config runner
  result : ConversationRunResult cfg
  serverExit : UInt32
  serverStderr : String
  base_url_eq : config.baseUrl = localBaseUrl port
  server_exit_eq : serverExit = 0

namespace LocalProbeResult

theorem complete_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner}
    (result : LocalProbeResult cfg runner) :
    result.prepared.plan.source.stream = false :=
  result.prepared.complete_mode

theorem base_url_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner}
    (result : LocalProbeResult cfg runner) :
    result.config.baseUrl = localBaseUrl result.port :=
  result.base_url_eq

theorem server_exited_successfully
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner}
    (result : LocalProbeResult cfg runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end LocalProbeResult

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

private def serverArgs (responses : List String) : Array String :=
  #[("-u" : String), "-c", serverScript] ++ responses.toArray

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

private def runChild
    {Model Capability : Type}
    (source : RequestSource)
    (fuel : Nat)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey)
    (child : IO.Process.Child serverStdio)
    (stderrTask : Task (Except IO.Error String)) :
    IO (Except LocalHttpError (LocalProbeResult cfg runner)) := do
  try
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let portLine ← stdout.getLine
    match parsePort portLine with
    | none =>
        stopServer child stderrTask
        pure (.error (.port portLine))
    | some port =>
        let config : ProbeConfig := {
          baseUrl := localBaseUrl port
          source
          fuel
        }
        match ← DeepSeekHarnessLiveProbe.runWithKey config key
            (curlTransport {}) cfg before runner with
        | .error error =>
            stopServer child stderrTask
            pure (.error (.request error))
        | .ok ⟨prepared, result⟩ =>
            let serverExit ← child.wait
            let serverStderr ← IO.ofExcept stderrTask.get
            let reportLine ← stdout.getLine
            match parseReport reportLine with
            | none =>
                pure (.error (.report reportLine))
            | some (requests, validRequests) =>
                if hExit : serverExit = 0 then
                  pure (.ok {
                    port
                    requests
                    validRequests
                    config
                    prepared
                    result
                    serverExit
                    serverStderr
                    base_url_eq := rfl
                    server_exit_eq := hExit
                  })
                else
                  pure (.error (.server serverExit serverStderr))
  catch error =>
    stopServer child stderrTask
    pure (.error (.io (toString error)))

private def runNonempty
    {Model Capability : Type}
    (source : RequestSource)
    (fuel : Nat)
    (responses : List String)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalHttpError (LocalProbeResult cfg runner)) := do
  try
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := serverArgs responses
      stdin := serverStdio.stdin
      stdout := serverStdio.stdout
      stderr := serverStdio.stderr
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    runChild source fuel cfg before runner key child stderrTask
  catch error =>
    pure (.error (.io (toString error)))

def runWithKey
    {Model Capability : Type}
    (source : RequestSource)
    (fuel : Nat)
    (responses : List String)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (key : ApiKey) :
    IO (Except LocalHttpError (LocalProbeResult cfg runner)) := do
  if responses.isEmpty then
    pure (.error .emptyResponses)
  else
    runNonempty source fuel responses cfg before runner key

/-! ## Executable two-round proof witness -/

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def responses : List String := [
  DeepSeekHarness.counterResponseBody,
  DeepSeekHarness.counterFinalResponseBody
]

def run : IO (Except LocalHttpError
    (LocalProbeResult Cordis.Harness.counterConfig runner)) :=
  runWithKey DeepSeekHarness.counterRequestSource 2 responses
    Cordis.Harness.counterConfig 0 runner { value := "fixture-key" }

structure Summary where
  requests : Nat
  validRequests : Nat
  rounds : Nat
  finalNextSeq : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def expectedSummary : Summary := {
  requests := 2
  validRequests := 2
  rounds := 2
  finalNextSeq := 4
  completed := true
}

def summarize
    (result : LocalProbeResult Cordis.Harness.counterConfig runner) : Summary := {
  requests := result.requests
  validRequests := result.validRequests
  rounds := result.result.rounds.length
  finalNextSeq := result.result.runner.session.nextSeq
  completed := result.result.stop.isCompleted
}

theorem expectedSummary_complete : expectedSummary.completed = true := rfl

end Example

end Cordis.DeepSeekHarnessLocalHttp
