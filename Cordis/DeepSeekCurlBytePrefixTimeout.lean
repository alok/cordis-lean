import Cordis.DeepSeekCurlBytePrefix
import Std.Async.Basic
import Std.Async.Timer

/-!
# Timer-driven process-byte prefixes

`DeepSeekCurlBytePrefix` proves the byte-framing and SSE-prefix equations for a synchronous
configured process reader.  This module adds a deadline around each blocking `stdout.read`.
The returned dependent result keeps the byte-prefix state, raw chunks, pending fragment, status,
stderr, exit code, and the exact timeout line index.  A timer win kills and waits the configured
child before returning.

This is still a local process boundary.  It does not claim arbitrary descendant cleanup,
fairness, backpressure, provider or executable authenticity, crash durability, reconnect
semantics, or equivalence to a deployed DeepSeek Harness.  The timeout wrapper is executable;
the typed theorems only describe the state retained by that wrapper.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlBytePrefixTimeout

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlByteFraming
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamByteFraming
open Cordis.DeepSeekStreamIncremental

inductive BytePrefixTimeoutStop (policy : LinePolicy) (state : BytePrefixState) where
  | completed (validated : ValidatedByteStream)
  | fuelExhausted
  | cancelled
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true)
  | timedOut (line : Nat) (timeoutMs : UInt32)
namespace BytePrefixTimeoutStop

def isCompleted {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixTimeoutStop policy state → Bool
  | .completed _ => true
  | .fuelExhausted | .cancelled .. | .timedOut .. => false

def isFuelExhausted {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixTimeoutStop policy state → Bool
  | .completed _ | .cancelled .. | .timedOut .. => false
  | .fuelExhausted => true

def isCancelled {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixTimeoutStop policy state → Bool
  | .completed _ | .fuelExhausted | .timedOut .. => false
  | .cancelled .. => true

def isTimedOut {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixTimeoutStop policy state → Bool
  | .completed _ | .fuelExhausted | .cancelled .. => false
  | .timedOut .. => true

end BytePrefixTimeoutStop

structure TimedBytePrefixResponse (policy : LinePolicy) where
  state : BytePrefixState
  rawChunks : List ByteArray
  pendingRaw : List UInt8
  pendingLine : Option (List UInt8)
  status : Option Nat
  statusSeen : Bool
  stop : BytePrefixTimeoutStop policy state
  stop_line : match stop with
    | .cancelled line _ _ => line = state.typed.line
    | .timedOut line _ => line = state.typed.line
    | .completed _ | .fuelExhausted => True
  rawBytes : ByteArray
  raw_chunks_eq : concatChunks rawChunks = rawBytes
  exitCode : Option UInt32
  stderr : String

namespace TimedBytePrefixResponse

def isCompleted {policy : LinePolicy} (response : TimedBytePrefixResponse policy) : Bool :=
  BytePrefixTimeoutStop.isCompleted response.stop

def isFuelExhausted {policy : LinePolicy} (response : TimedBytePrefixResponse policy) : Bool :=
  BytePrefixTimeoutStop.isFuelExhausted response.stop

def isCancelled {policy : LinePolicy} (response : TimedBytePrefixResponse policy) : Bool :=
  BytePrefixTimeoutStop.isCancelled response.stop

def isTimedOut {policy : LinePolicy} (response : TimedBytePrefixResponse policy) : Bool :=
  BytePrefixTimeoutStop.isTimedOut response.stop

theorem timeout_line_eq_prefix
    {policy : LinePolicy}
    (response : TimedBytePrefixResponse policy)
    {line : Nat} {timeoutMs : UInt32}
    (stop_eq : response.stop = .timedOut line timeoutMs) :
    line = response.state.typed.line := by
  simpa [stop_eq] using response.stop_line

end TimedBytePrefixResponse

private structure IngressState where
  state : BytePrefixState
  pending : List UInt8
  pendingLine : Option (List UInt8)
  statusSeen : Bool

private def pushBodyLine
    (state : BytePrefixState)
    (bytes : List UInt8) : Except BytePrefixClientError BytePrefixState :=
  match pushChunk state (bytesOfList (bytes ++ [10])) with
  | .error error => .error (.framing error)
  | .ok next => .ok next

private def consumeOutputLines
    (state : BytePrefixState)
    (statusSeen : Bool)
    (pendingLine : Option (List UInt8))
    (lines : List (List UInt8)) :
    Except BytePrefixClientError (BytePrefixState × Bool × Option (List UInt8)) :=
  match lines with
  | [] => .ok ⟨state, statusSeen, pendingLine⟩
  | bytes :: rest =>
      if statusSeen then
        consumeOutputLines state true none rest
      else
        match String.fromUTF8? (bytesOfList bytes) with
        | none =>
            .error (.framing (.invalidUtf8 state.typed.line (bytesOfList bytes)))
        | some line =>
            if isStatusLine line then
              consumeOutputLines state true none rest
            else
              match pendingLine with
              | none =>
                  match bytes with
                  | [] => consumeOutputLines state false (some bytes) rest
                  | _ =>
                      match pushBodyLine state bytes with
                      | .error error => .error error
                      | .ok next => consumeOutputLines next false none rest
              | some previous =>
                  match pushBodyLine state previous with
                  | .error error => .error error
                  | .ok next =>
                      match bytes with
                      | [] => consumeOutputLines next false (some bytes) rest
                      | _ =>
                          match pushBodyLine next bytes with
                          | .error error => .error error
                          | .ok final => consumeOutputLines final false none rest

private def pushOutputChunk
    (state : BytePrefixState)
    (pending : List UInt8)
    (pendingLine : Option (List UInt8))
    (statusSeen : Bool)
    (chunk : ByteArray) :
    Except BytePrefixClientError IngressState :=
  let split := splitComplete (pending ++ chunk.toList)
  match consumeOutputLines state statusSeen pendingLine split.1 with
  | .error error => .error error
  | .ok ⟨next, nextStatusSeen, nextPendingLine⟩ =>
      .ok {
        state := next
        pending := split.2
        pendingLine := nextPendingLine
        statusSeen := nextStatusSeen
      }

private def cleanup
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
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

private def finishObserved
    (policy : LinePolicy)
    (state : BytePrefixState)
    (pending : List UInt8)
    (pendingLine : Option (List UInt8))
    (statusSeen : Bool)
    (rawChunks : List ByteArray)
    (exitCode : UInt32)
    (stderr : String) :
    Except BytePrefixClientError (TimedBytePrefixResponse policy) :=
  if exitCode != 0 then
    .error (.process (.exited exitCode stderr))
  else if pending != [] then
    .error (.framing (.incomplete (bytesOfList pending)))
  else
    let finishedState : Except BytePrefixClientError BytePrefixState :=
      match pendingLine with
      | none => .ok state
      | some bytes =>
          if statusSeen then
            .ok state
          else
            match pushBodyLine state bytes with
            | .error error => .error error
            | .ok next => .ok next
    match finishedState with
    | .error error => .error error
    | .ok finalState =>
        let rawBytes := concatChunks rawChunks
        match String.fromUTF8? rawBytes with
        | none => .error (.framing (.invalidUtf8 finalState.typed.line rawBytes))
        | some rawText =>
            match parseOutput rawText with
            | .error error => .error (.process error)
            | .ok response =>
                if response.status < 200 || response.status ≥ 300 then
                  .error (.httpStatus response.status response.body)
                else
                  match DeepSeekStreamByteFraming.finish finalState with
                  | .error error => .error (.framing error)
                  | .ok stream =>
                      if stream.text = response.body then
                        if bytesOfList finalState.source = response.body.toUTF8 then
                          .ok {
                            state := finalState
                            rawChunks
                            pendingRaw := pending
                            pendingLine := none
                            status := some response.status
                            statusSeen
                            stop := .completed stream
                            stop_line := trivial
                            rawBytes
                            raw_chunks_eq := rfl
                            exitCode := some exitCode
                            stderr
                          }
                        else
                          .error .sourceMismatch
                      else
                        .error (.bodyMismatch response.body stream.text)

private inductive TimedChunk where
  | chunk (value : ByteArray)
  | eof (exitCode : UInt32)
  | timedOut
  | io (message : String)
deriving Inhabited

private def readChunkWithTimeout
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stdout : IO.FS.Stream)
    (chunkSize : Nat)
    (timeoutMs : UInt32) : IO TimedChunk := do
  let sleeper ← Std.Async.Async.block <|
    Std.Async.Sleep.mk (Std.Time.Millisecond.Offset.ofNat timeoutMs.toNat)
  let timeoutRef ← IO.mkRef false
  let readTask ← IO.asTask do
    try
      let chunk ← stdout.read chunkSize.toUSize
      if chunk.isEmpty then
        let exitCode ← child.wait
        pure (.eof exitCode)
      else
        pure (.chunk chunk)
    catch error =>
      pure (.io (toString error))
  let readAction : Std.Async.Async TimedChunk := do
    try
      Std.Async.Async.ofAsyncTask readTask
    catch error =>
      pure (.io (toString error))
  let timeoutAction : Std.Async.Async TimedChunk := do
    sleeper.wait
    timeoutRef.set true
    try
      child.kill
    catch _ =>
      pure ()
    pure .timedOut
  try
    let result ← Std.Async.Async.block (Std.Async.Async.race readAction timeoutAction)
    let timerWon ← timeoutRef.get
    if timerWon || result matches .timedOut then
      if !timerWon then
        timeoutRef.set true
        try
          child.kill
        catch _ =>
          pure ()
      try
        discard <| IO.wait readTask
      catch _ =>
        pure ()
      pure .timedOut
    else if result matches .chunk _ | .eof _ then
      sleeper.stop
      pure result
    else
      pure result
  catch error =>
    pure (.io (toString error))

private def runBytePrefixTimeoutLoop
    (policy : LinePolicy)
    (fuel chunkSize : Nat)
    (timeoutMs : UInt32)
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String))
    (stdout : IO.FS.Stream)
    (state : BytePrefixState)
    (pending : List UInt8)
    (pendingLine : Option (List UInt8))
    (statusSeen : Bool)
    (rawChunksRev : List ByteArray) :
    IO (Except BytePrefixClientError (TimedBytePrefixResponse policy)) := do
  match fuel with
  | 0 =>
      cleanup child stderrTask
      let rawChunks := rawChunksRev.reverse
      let rawBytes := concatChunks rawChunks
      pure (.ok {
        state
        rawChunks
        pendingRaw := pending
        pendingLine
        status := none
        statusSeen
        stop := .fuelExhausted
        stop_line := trivial
        rawBytes
        raw_chunks_eq := rfl
        exitCode := none
        stderr := ""
      })
  | fuel + 1 =>
      if decided : policy.decide state.typed.line then
        cleanup child stderrTask
        let rawChunks := rawChunksRev.reverse
        let rawBytes := concatChunks rawChunks
        pure (.ok {
          state
          rawChunks
          pendingRaw := pending
          pendingLine
          status := none
          statusSeen
          stop := .cancelled state.typed.line policy.reason decided
          stop_line := rfl
          rawBytes
          raw_chunks_eq := rfl
          exitCode := none
          stderr := ""
        })
      else
        try
          match ← readChunkWithTimeout child stdout chunkSize timeoutMs with
          | .timedOut =>
              let stderr ← try IO.ofExcept stderrTask.get catch _ => pure ""
              let rawChunks := rawChunksRev.reverse
              let rawBytes := concatChunks rawChunks
              pure <| .ok {
                state
                rawChunks
                pendingRaw := pending
                pendingLine
                status := none
                statusSeen
                stop := .timedOut state.typed.line timeoutMs
                stop_line := rfl
                rawBytes
                raw_chunks_eq := rfl
                exitCode := none
                stderr
              }
          | .io message =>
              cleanup child stderrTask
              pure (.error (.io message))
          | .chunk chunk =>
              if chunk.isEmpty then
                let exitCode ← child.wait
                let stderr ← IO.ofExcept stderrTask.get
                pure <| finishObserved policy state pending pendingLine statusSeen
                  rawChunksRev.reverse exitCode stderr
              else
                match pushOutputChunk state pending pendingLine statusSeen chunk with
                | .error error =>
                    cleanup child stderrTask
                    pure (.error error)
                | .ok next =>
                    runBytePrefixTimeoutLoop policy fuel chunkSize timeoutMs child stderrTask
                      stdout next.state next.pending next.pendingLine next.statusSeen
                      (chunk :: rawChunksRev)
          | .eof exitCode =>
              if exitCode == 137 then
                let stderr ← try IO.ofExcept stderrTask.get catch _ => pure ""
                let rawChunks := rawChunksRev.reverse
                let rawBytes := concatChunks rawChunks
                pure <| .ok {
                  state
                  rawChunks
                  pendingRaw := pending
                  pendingLine
                  status := none
                  statusSeen
                  stop := .timedOut state.typed.line timeoutMs
                  stop_line := rfl
                  rawBytes
                  raw_chunks_eq := rfl
                  exitCode := some exitCode
                  stderr
                }
              else
                let stderr ← IO.ofExcept stderrTask.get
                pure <| finishObserved policy state pending pendingLine statusSeen
                  rawChunksRev.reverse exitCode stderr
        catch error =>
          cleanup child stderrTask
          pure (.error (.io (toString error)))

def executeSseBytePrefixWithTimeout
    (policy : LinePolicy)
    (maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except BytePrefixClientError (TimedBytePrefixResponse policy)) := do
  if chunkSize = 0 then
    pure (.error .chunkSize)
  else
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
      runBytePrefixTimeoutLoop policy maxReads chunkSize timeoutMs child stderrTask
        (IO.FS.Stream.ofHandle child.stdout) BytePrefixState.initial [] none false []
    catch error =>
      pure (.error (.io (toString error)))

def blockedBytePrefixProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #["-c", "cat >/dev/null; exec sleep 2", "cordis-byte-prefix-timeout"]

def delayedBytePrefixProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "printf '%s' \"$1\"; printf 'timeout-stderr\\n' >&2;
      exec sleep 2",
    "cordis-byte-prefix-timeout-delayed",
    DeepSeekStream.exampleStreamBody
  ]

def blockedBytePrefixProcessRun :
    IO (Except BytePrefixClientError (TimedBytePrefixResponse (LinePolicy.never))) :=
  executeSseBytePrefixWithTimeout (LinePolicy.never) 32 4096 100 blockedBytePrefixProcess
    DeepSeekCurlTransport.fixtureRequest.request

def delayedBytePrefixProcessRun :
    IO (Except BytePrefixClientError (TimedBytePrefixResponse (LinePolicy.never))) :=
  executeSseBytePrefixWithTimeout (LinePolicy.never) 4096 1 100 delayedBytePrefixProcess
    DeepSeekCurlTransport.fixtureRequest.request

def fastBytePrefixProcessRun :
    IO (Except BytePrefixClientError (TimedBytePrefixResponse (LinePolicy.never))) :=
  executeSseBytePrefixWithTimeout (LinePolicy.never) 4096 1 2000
    (DeepSeekCurlBytePrefix.fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

theorem timeout_entry_eq_prefix
    {policy : LinePolicy}
    (response : TimedBytePrefixResponse policy)
    {line : Nat} {timeoutMs : UInt32}
    (stop_eq : response.stop = .timedOut line timeoutMs) :
    line = response.state.typed.line :=
  response.timeout_line_eq_prefix stop_eq

end Cordis.DeepSeekCurlBytePrefixTimeout
