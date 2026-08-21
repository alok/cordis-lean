import Cordis.DeepSeekStreamIncremental
import Cordis.DeepSeekCurlIncremental

/-!
# Process-backed proof-carrying DeepSeek SSE prefixes

`DeepSeekStreamIncremental` gives a pure state machine for complete SSE lines. This module brings
that state to the existing piped-process boundary: every body line is normalized and fed into the
typed prefix state before the next read, while the raw process body and status remain available at
the terminal boundary. A caller-controlled `LinePolicy` can stop before a subsequent read, and
the child is then killed and waited before the result is returned.

This is deliberately a line-oriented process adapter. It does not claim byte framing,
backpressure, asynchronous cancellation of a blocked read, reconnect semantics, credential or
executable trust, provider-complete assembly, or equivalence to a deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlPrefix

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamIncremental

inductive PrefixClientError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | stream (error : StreamError)
  | lineLimit (reads : Nat)
  | io (message : String)
deriving DecidableEq, Repr

structure PrefixResponse (policy : LinePolicy) where
  state : PrefixState
  rawBody : String
  status : Option Nat
  stop : StreamStop policy state

namespace PrefixResponse

def isCompleted {policy : LinePolicy} (response : PrefixResponse policy) : Bool :=
  response.stop.isCompleted

def isFuelExhausted {policy : LinePolicy} (response : PrefixResponse policy) : Bool :=
  response.stop.isFuelExhausted

def isCancelled {policy : LinePolicy} (response : PrefixResponse policy) : Bool :=
  response.stop.isCancelled

end PrefixResponse

private def dropLineEnding (line : String) : String :=
  if line.endsWith "\n" then (line.dropEnd 1).toString else line

private def cleanup
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String)) : IO Unit := do
  killAndWait child
  try
    let _ ← IO.ofExcept stderrTask.get
    pure ()
  catch _ =>
    pure ()

private def finishObserved
    (policy : LinePolicy)
    (state : PrefixState)
    (rawOutput : String)
    (statusSeen : Bool)
    (exitCode : UInt32)
    (stderr : String) : Except PrefixClientError (PrefixResponse policy) :=
  if exitCode != 0 then
    .error (.process (.exited exitCode stderr))
  else if !statusSeen then
    .error (.process (.malformedOutput rawOutput))
  else
    match parseOutput rawOutput with
    | .error error => .error (.process error)
    | .ok response =>
        if response.status < 200 || response.status ≥ 300 then
          .error (.httpStatus response.status response.body)
        else
          match finish state with
          | .error error => .error (.stream error)
          | .ok validated =>
              .ok {
                state
                rawBody := response.body
                status := some response.status
                stop := .completed validated
              }

def executeSsePrefix
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except PrefixClientError (PrefixResponse policy)) := do
  try
    let child ← IO.Process.spawn {
      cmd := config.command
      args := config.args request
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let (stdin, child) ← child.takeStdin
    stdin.putStr request.body
    stdin.flush
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    let stdout := IO.FS.Stream.ofHandle child.stdout
    let rec loop
        (fuel : Nat)
        (state : PrefixState)
        (rawOutput : String)
        (statusSeen : Bool) : IO (Except PrefixClientError (PrefixResponse policy)) := do
      match fuel with
      | 0 =>
          cleanup child stderrTask
          pure (.ok {
            state
            rawBody := rawOutput
            status := none
            stop := .fuelExhausted
          })
      | fuel + 1 =>
          if decided : policy.decide state.line then
            cleanup child stderrTask
            pure (.ok {
              state
              rawBody := rawOutput
              status := none
              stop := .cancelled state.line policy.reason decided
            })
          else
            let line ← stdout.getLine
            if line.isEmpty then
              let exitCode ← child.wait
              let stderr ← IO.ofExcept stderrTask.get
              pure <| finishObserved policy state rawOutput statusSeen exitCode stderr
            else if statusSeen then
              loop fuel state (rawOutput ++ line) true
            else if isStatusLine line then
              loop fuel state (rawOutput ++ line) true
            else
              match pushLine state (dropLineEnding line) with
              | .error error =>
                  cleanup child stderrTask
                  pure (.error (.stream error))
              | .ok next => loop fuel next (rawOutput ++ line) false
    loop maxReads PrefixState.initial "" false
  catch error =>
    pure (.error (.io (toString error)))

def executeSsePrefixNoop
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :=
  executeSsePrefix policy maxReads config request

def fixtureProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-prefix-fixture",
    DeepSeekStream.exampleStreamBody
  ]

def fixtureResponse : IO (Except PrefixClientError
    (PrefixResponse (LinePolicy.never))) :=
  executeSsePrefix (LinePolicy.never) 64 fixtureProcess DeepSeekCurlTransport.fixtureRequest.request

end Cordis.DeepSeekCurlPrefix
