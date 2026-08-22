import Cordis.DeepSeekHarnessLocalSse
import Cordis.DeepSeekStreamIncremental
import Std.Async.Basic
import Std.Async.Timer

/-!
# Loopback HTTP SSE blocked-read timeout

`DeepSeekHarnessLocalSse` and `DeepSeekHarnessLocalSseRetry` exercise real curl requests against
loopback HTTP servers.  This module adds the missing in-flight boundary: the server flushes a
valid SSE prefix, pauses before the next line, and a real asynchronous timer races the blocking
curl stdout read.  A timeout kills and waits for the configured curl child and retains the exact
typed SSE prefix instead of fabricating a completed assistant.  A fast fixture follows the same
path to a completed text append.

This is local configured-process evidence only.  It does not claim arbitrary descendant cleanup,
fairness, backpressure, credential or TLS authenticity, provider-complete assembly, reconnect
semantics, or deployed Harness cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseTimeout

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental

private def timeoutServerScript : String :=
  "import http.server,json,sys,time\n" ++
  "body=sys.argv[1].encode()\n" ++
  "delay=float(sys.argv[2])/1000.0\n" ++
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
  "      lines=payload.splitlines(True)\n" ++
  "      for line in lines[:2]:\n" ++
  "        self.wfile.write(line)\n" ++
  "        self.wfile.flush()\n" ++
  "      time.sleep(delay)\n" ++
  "      for line in lines[2:]:\n" ++
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

private def serverArgs (body : String) (delayMs : UInt32) : Array String :=
  #[("-u" : String), "-c", timeoutServerScript, body, toString delayMs]

private def serverStdio : IO.Process.StdioConfig where
  stdin := .null
  stdout := .piped
  stderr := .piped

private inductive TimedRead where
  | line (line : String)
  | timedOut
  | io (message : String)
deriving Inhabited

private def readLineWithTimeout
    {config : IO.Process.StdioConfig}
    (child : IO.Process.Child config)
    (stdout : IO.FS.Stream)
    (timeoutMs : UInt32) : IO TimedRead := do
  let sleeper ← Std.Async.Async.block <|
    Std.Async.Sleep.mk (Std.Time.Millisecond.Offset.ofNat timeoutMs.toNat)
  let readTask ← IO.asTask stdout.getLine
  let readAction : Std.Async.Async TimedRead := do
    try
      let line ← Std.Async.Async.ofAsyncTask readTask
      pure (.line line)
    catch error =>
      pure (.io (toString error))
  let timeoutAction : Std.Async.Async TimedRead := do
    sleeper.wait
    try
      child.kill
    catch _ =>
      pure ()
    pure .timedOut
  try
    let result ← Std.Async.Async.block (Std.Async.Async.race readAction timeoutAction)
    if result matches .line _ then
      sleeper.stop
    if result matches .timedOut then
      try
        discard <| IO.wait readTask
      catch _ =>
        pure ()
    pure result
  catch error =>
    pure (.io (toString error))

private def stopChild
    {config : IO.Process.StdioConfig}
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

private def stripLineEnding (line : String) : String :=
  if line.endsWith "\n" then (line.dropEnd 1).toString else line

structure PreparedTimeoutRequest
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl key source runner.session = .ok plan

namespace PreparedTimeoutRequest

theorem streaming_mode
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedTimeoutRequest baseUrl source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {source : RequestSource} {runner : ConversationRunner}
    (prepared : PreparedTimeoutRequest baseUrl source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedTimeoutRequest

inductive LocalSseTimeoutError where
  | emptyBody
  | request (error : RequestError)
  | stream (error : IncrementalError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | port (line : String)
  | report (line : String)
  | server (code : UInt32) (stderr : String)
  | io (message : String)
deriving DecidableEq, Repr

structure TimedPrefix
    (source : RequestSource)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedTimeoutRequest (localBaseUrl port) source runner
  state : PrefixState
  lines : List String
  timeoutMs : UInt32
  serverExit : Option UInt32
  serverStderr : String

namespace TimedPrefix

theorem streaming_mode
    {source : RequestSource} {runner : ConversationRunner}
    (pfx : TimedPrefix source runner) :
    pfx.prepared.plan.source.stream = true :=
  pfx.prepared.streaming_mode

theorem is_not_done
    {source : RequestSource} {runner : ConversationRunner}
    (pfx : TimedPrefix source runner)
    (notDone : pfx.state.done = false) :
    pfx.state.done = false :=
  notDone

end TimedPrefix

structure Completed
    (source : RequestSource)
    (runner : ConversationRunner) where
  port : Nat
  prepared : PreparedTimeoutRequest (localBaseUrl port) source runner
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

namespace Completed

theorem append_endpoint
    {source : RequestSource} {runner : ConversationRunner}
    (result : Completed source runner) :
    result.after =
      ConversationRunner.appendFinished runner result.finished [] (by simp) (by simp) :=
  result.append_eq

theorem nextSeq
    {source : RequestSource} {runner : ConversationRunner}
    (result : Completed source runner) :
    result.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [result.append_eq]
  exact ConversationRunner.appendFinished_nextSeq runner result.finished [] (by simp) (by simp)

theorem server_exited_successfully
    {source : RequestSource} {runner : ConversationRunner}
    (result : Completed source runner) :
    result.serverExit = 0 :=
  result.server_exit_eq

end Completed

inductive Outcome
    (source : RequestSource)
    (runner : ConversationRunner) where
  | timedOut (pfx : TimedPrefix source runner)
  | completed (result : Completed source runner)

namespace Outcome

def isTimedOut {source : RequestSource} {runner : ConversationRunner} :
    Outcome source runner → Bool
  | .timedOut _ => true
  | .completed _ => false

def isCompleted {source : RequestSource} {runner : ConversationRunner} :
    Outcome source runner → Bool
  | .timedOut _ => false
  | .completed _ => true

end Outcome

private def parsePrepared
    (baseUrl : String)
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey) :
    Except RequestError (PreparedTimeoutRequest baseUrl source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl key source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

private inductive ReadStop where
  | timedOut
      (state : PrefixState)
      (output : String)
      (lines : List String)
  | completed
      (state : PrefixState)
      (output : String)
      (lines : List String)
      (exitCode : UInt32)
      (stderr : String)

private def readPrefix
    (fuel : Nat)
    (timeoutMs : UInt32)
    {config : IO.Process.StdioConfig}
    (child : IO.Process.Child config)
    (stderrTask : Task (Except IO.Error String))
    (stdout : IO.FS.Stream)
    (state : PrefixState)
    (output : String)
    (lines : List String)
    (statusSeen : Bool) :
    IO (Except LocalSseTimeoutError ReadStop) := do
  match fuel with
  | 0 =>
      stopChild child stderrTask
      pure (.error (.stream (.lineLimit lines.length)))
  | fuel + 1 =>
      match ← readLineWithTimeout child stdout timeoutMs with
      | .timedOut =>
          stopChild child stderrTask
          pure <| .ok (.timedOut state output lines)
      | .io message =>
          stopChild child stderrTask
          pure (.error (.io message))
      | .line line =>
          if line.isEmpty then
            let exitCode ← child.wait
            let stderr ← IO.ofExcept stderrTask.get
            pure (.ok (.completed state output lines exitCode stderr))
          else
            let nextOutput := output ++ line
            if statusSeen then
              readPrefix fuel timeoutMs child stderrTask stdout state nextOutput lines true
            else if isStatusLine line then
              readPrefix fuel timeoutMs child stderrTask stdout state nextOutput lines true
            else
              let normalized := stripLineEnding line
              match _pushed : pushLine state normalized with
              | .error error =>
                  stopChild child stderrTask
                  pure (.error (.stream (.stream error)))
              | .ok nextState =>
                  readPrefix fuel timeoutMs child stderrTask stdout nextState nextOutput
                    (normalized :: lines) statusSeen

private def runChild
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (maxReads : Nat)
    (timeoutMs : UInt32)
    (serverChild : IO.Process.Child serverStdio)
    (serverStderrTask : Task (Except IO.Error String)) :
    IO (Except LocalSseTimeoutError (Outcome source runner)) := do
  try
    let serverStdout := IO.FS.Stream.ofHandle serverChild.stdout
    let portLine ← serverStdout.getLine
    match parsePort portLine with
    | none =>
        stopChild serverChild serverStderrTask
        pure (.error (.port portLine))
    | some port =>
        let baseUrl := localBaseUrl port
        match parsePrepared baseUrl source runner key with
        | .error error =>
            stopChild serverChild serverStderrTask
            pure (.error (.request error))
        | .ok prepared =>
            let process := curlProcess { extraArgs := #["--no-buffer"] }
            let curlChild ← IO.Process.spawn {
              cmd := process.command
              args := process.args prepared.plan.request
              stdin := .piped
              stdout := .piped
              stderr := .piped
            }
            let (stdin, curlChild) ← curlChild.takeStdin
            stdin.putStr prepared.plan.request.body
            stdin.flush
            let curlStderrTask ← IO.asTask curlChild.stderr.readToEnd Task.Priority.dedicated
            match ← readPrefix maxReads timeoutMs curlChild curlStderrTask
                (IO.FS.Stream.ofHandle curlChild.stdout) PrefixState.initial "" [] false with
            | .error error =>
                stopChild serverChild serverStderrTask
                pure (.error error)
            | .ok (.timedOut state output lines) =>
                stopChild serverChild serverStderrTask
                pure <| .ok <| .timedOut {
                  port
                  prepared
                  state
                  lines := lines.reverse
                  timeoutMs
                  serverExit := none
                  serverStderr := ""
                }
            | .ok (.completed state output lines curlExit curlStderr) =>
                let serverExit ← serverChild.wait
                let serverStderr ← IO.ofExcept serverStderrTask.get
                let reportLine ← serverStdout.getLine
                if curlExit != 0 then
                  pure (.error (.stream (.process (.exited curlExit curlStderr))))
                else if hServer : serverExit = 0 then
                  match parseReport reportLine with
                  | none => pure (.error (.report reportLine))
                  | some (requests, validRequests) =>
                      match parseOutput output with
                      | .error error => pure (.error (.stream (.process error)))
                      | .ok response =>
                          if response.status < 200 || response.status ≥ 300 then
                            pure (.error (.stream (.httpStatus response.status response.body)))
                          else
                            match validateSse response.body with
                            | .error error => pure (.error (.stream (.stream error)))
                            | .ok wire =>
                                let incremental : IncrementalResponse response.body := {
                                  status := response.status
                                  lines := lines.reverse
                                  wire
                                }
                                match finishText response.body with
                                | .error error => pure (.error (.response error))
                                | .ok finished =>
                                    pure <| .ok <| .completed {
                                      port
                                      prepared
                                      body := response.body
                                      response := incremental
                                      finished
                                      after := ConversationRunner.appendFinished runner finished []
                                        (by simp) (by simp)
                                      append_eq := rfl
                                      requests
                                      validRequests
                                      serverExit
                                      serverStderr
                                      server_exit_eq := hServer
                                    }
                else
                  pure (.error (.server serverExit serverStderr))
  catch error =>
    stopChild serverChild serverStderrTask
    pure (.error (.io (toString error)))

def runWithTimeout
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (delayMs : UInt32)
    (maxReads : Nat := 64)
    (timeoutMs : UInt32 := 100) :
    IO (Except LocalSseTimeoutError (Outcome source runner)) := do
  if body.isEmpty then
    pure (.error .emptyBody)
  else
    try
      let child ← IO.Process.spawn {
        cmd := "python3"
        args := serverArgs body delayMs
        stdin := serverStdio.stdin
        stdout := serverStdio.stdout
        stderr := serverStdio.stderr
      }
      let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
      runChild source runner key maxReads timeoutMs child stderrTask
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

def timeoutRun : IO (Except LocalSseTimeoutError
    (Outcome DeepSeekHarness.counterRequestSource runner)) :=
  runWithTimeout DeepSeekHarness.counterRequestSource runner { value := "fixture-key" }
    body 400 64 100

def fastRun : IO (Except LocalSseTimeoutError
    (Outcome DeepSeekHarness.counterRequestSource runner)) :=
  runWithTimeout DeepSeekHarness.counterRequestSource runner { value := "fixture-key" }
    body 0 64 2000

structure Summary where
  timedOut : Bool
  acceptedLines : Nat
  nextSeq : Nat
  requests : Nat
  validRequests : Nat
deriving BEq, DecidableEq, Repr

def summarize : Outcome DeepSeekHarness.counterRequestSource runner → Summary
  | .timedOut pfx => {
      timedOut := true
      acceptedLines := pfx.lines.length
      nextSeq := runner.session.nextSeq
      requests := 1
      validRequests := 1
    }
  | .completed result => {
      timedOut := false
      acceptedLines := result.response.lines.length
      nextSeq := result.after.session.nextSeq
      requests := result.requests
      validRequests := result.validRequests
    }

def expectedTimeout : Summary := {
  timedOut := true
  acceptedLines := 2
  nextSeq := 1
  requests := 1
  validRequests := 1
}

def expectedFast : Summary := {
  timedOut := false
  acceptedLines := 7
  nextSeq := 2
  requests := 1
  validRequests := 1
}

theorem expectedTimeout_isTimedOut : expectedTimeout.timedOut = true := rfl

theorem expectedFast_isCompleted : expectedFast.timedOut = false := rfl

end Example

end Cordis.DeepSeekHarnessLocalSseTimeout
