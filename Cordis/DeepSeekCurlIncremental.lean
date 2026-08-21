import Cordis.DeepSeekCurlStream

/-!
# Line-oriented process-backed DeepSeek SSE

This module adds the next runtime seam after `DeepSeekCurlStream`: a configured process is spawned
with piped standard streams, request bytes are written to stdin, and each complete stdout line from
the response body is delivered to a caller callback before the final status trailer is consumed.
The returned value still retains the exact reconstructed body and the strict `ValidatedSseStream`
certificate, so the callback stream is evidence rather than an erased side channel.

The adapter deliberately remains line-oriented and complete-response validated. It requires an
explicit read budget and does not claim byte-level framing, bounded buffering, backpressure,
cancellation, reconnects, credential validity, executable trust, or equivalence to a deployed
DeepSeek stream assembler.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlIncremental

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekStream

inductive IncrementalError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | stream (error : StreamError)
  | callback (line : Nat) (message : String)
  | lineLimit (reads : Nat)
  | io (message : String)
deriving DecidableEq, Repr

structure IncrementalResponse (body : String) where
  status : Nat
  lines : List String
  wire : ValidatedSseStream body

def statusPrefix : String := "__CORDIS_HTTP_STATUS__"

def isStatusLine (line : String) : Bool :=
  line.trimAscii.copy.startsWith statusPrefix

def readBodyLines
    (fuel : Nat)
    (stdout : IO.FS.Stream)
    (onLine : Nat → String → IO Unit)
    (lineIndex : Nat)
    (output : String)
    (lines : List String)
    (statusSeen : Bool) : IO (Except IncrementalError (String × List String)) :=
  match fuel with
  | 0 => pure (.error (.lineLimit lines.length))
  | fuel + 1 => do
      let line ← stdout.getLine
      if line.isEmpty then
        pure (.ok (output, lines.reverse))
      else
        let nextOutput := output ++ line
        if statusSeen then
          readBodyLines fuel stdout onLine lineIndex nextOutput lines true
        else if isStatusLine line then
          readBodyLines fuel stdout onLine lineIndex nextOutput lines true
        else
          try
            onLine lineIndex line
            readBodyLines fuel stdout onLine (lineIndex + 1) nextOutput (line :: lines) false
          catch error =>
            pure (.error (.callback lineIndex (toString error)))

def killAndWait {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try
    child.kill
  catch _ =>
    pure ()
  try
    discard <| child.wait
  catch _ =>
    pure ()

def executeSseIncremental
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (onLine : Nat → String → IO Unit) :
    IO (Except IncrementalError
      (Sigma fun body : String => IncrementalResponse body)) := do
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
    let observed ← try
      readBodyLines maxReads (IO.FS.Stream.ofHandle child.stdout) onLine 0 "" [] false
    catch error =>
      killAndWait child
      pure (.error (.io (toString error)))
    match observed with
    | .error error =>
        killAndWait child
        pure (.error error)
    | .ok ⟨output, lines⟩ =>
        let exitCode ← child.wait
        let stderr ← IO.ofExcept stderrTask.get
        if exitCode != 0 then
          pure (.error (.process (.exited exitCode stderr)))
        else
          match parseOutput output with
          | .error error => pure (.error (.process error))
          | .ok response =>
              if response.status < 200 || response.status ≥ 300 then
                pure (.error (.httpStatus response.status response.body))
              else
                match validateSse response.body with
                | .error error => pure (.error (.stream error))
                | .ok wire => pure (.ok ⟨response.body, {
                    status := response.status
                    lines
                    wire
                  }⟩)
  catch error =>
    pure (.error (.io (toString error)))

def executeSseIncrementalNoop
    (maxReads : Nat) (config : ProcessConfig) (request : HttpRequest) :=
  executeSseIncremental maxReads config request (fun _ _ => pure ())

def fixtureProcess (responseBody : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-incremental-fixture",
    responseBody
  ]

def fixtureResponse : IO (Except IncrementalError
    (Sigma fun body : String => IncrementalResponse body)) :=
  executeSseIncremental 64 (fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (fun _ _ => pure ())

end Cordis.DeepSeekCurlIncremental
