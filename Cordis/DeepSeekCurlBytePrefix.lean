import Cordis.DeepSeekStreamByteFraming
import Cordis.DeepSeekCurlByteFraming
import Cordis.DeepSeekCurlIncremental

/-!
# Process-backed byte-prefix DeepSeek SSE ingress

This module is the live process counterpart to DeepSeekStreamByteFraming: stdout is read in
bounded byte chunks, complete LF-delimited body lines are decoded and fed to the typed prefix
state before the next read, and bytes belonging to an incomplete line remain explicit in the
returned state. The private status trailer is recognized as a process boundary rather than passed
to the SSE parser. Completed responses retain the raw chunks, exact status/body parse, byte-prefix
certificate, and strict [DONE] validation.

The adapter is intentionally a bounded process reader. It does not claim network reachability,
credential validity, executable trust, interruption of a blocked read, backpressure, reconnects,
provider-complete assembly, or equivalence to a deployed DeepSeek Harness. A stop policy is
consulted before each subsequent byte read; a single read may contain several complete lines.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlBytePrefix

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamByteFraming
open Cordis.DeepSeekStreamIncremental

inductive BytePrefixClientError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | framing (error : ByteFramingError)
  | readLimit (reads : Nat)
  | chunkSize
  | bodyMismatch (expected : String) (actual : String)
  | sourceMismatch
  | io (message : String)
deriving DecidableEq

inductive BytePrefixStop (policy : LinePolicy) (state : BytePrefixState) where
  | completed (validated : ValidatedByteStream)
  | fuelExhausted
  | cancelled
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true)

namespace BytePrefixStop

def isCompleted {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixStop policy state -> Bool
  | .completed _ => true
  | .fuelExhausted | .cancelled _ _ _ => false

def isFuelExhausted {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixStop policy state -> Bool
  | .completed _ | .cancelled _ _ _ => false
  | .fuelExhausted => true

def isCancelled {policy : LinePolicy} {state : BytePrefixState} :
    BytePrefixStop policy state -> Bool
  | .completed _ | .fuelExhausted => false
  | .cancelled _ _ _ => true

end BytePrefixStop

structure BytePrefixResponse (policy : LinePolicy) where
  state : BytePrefixState
  rawChunks : List ByteArray
  pendingRaw : List UInt8
  pendingLine : Option (List UInt8)
  status : Option Nat
  statusSeen : Bool
  stop : BytePrefixStop policy state
  rawBytes : ByteArray
  raw_chunks_eq : DeepSeekCurlByteFraming.concatChunks rawChunks = rawBytes

namespace BytePrefixResponse

def isCompleted {policy : LinePolicy} (response : BytePrefixResponse policy) : Bool :=
  BytePrefixStop.isCompleted response.stop

def isFuelExhausted {policy : LinePolicy} (response : BytePrefixResponse policy) : Bool :=
  BytePrefixStop.isFuelExhausted response.stop

def isCancelled {policy : LinePolicy} (response : BytePrefixResponse policy) : Bool :=
  BytePrefixStop.isCancelled response.stop

end BytePrefixResponse

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
  killAndWait child
  try
    let _ ← IO.ofExcept stderrTask.get
    pure ()
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
    (stderr : String) : Except BytePrefixClientError (BytePrefixResponse policy) :=
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
        let rawBytes := DeepSeekCurlByteFraming.concatChunks rawChunks
        match _decoded : String.fromUTF8? rawBytes with
        | none => .error (.framing (.invalidUtf8 finalState.typed.line rawBytes))
        | some rawText =>
            match _parsed : parseOutput rawText with
            | .error error => .error (.process error)
            | .ok response =>
                if response.status < 200 || response.status ≥ 300 then
                  .error (.httpStatus response.status response.body)
                else
                  match _validated : DeepSeekStreamByteFraming.finish finalState with
                  | .error error => .error (.framing error)
                  | .ok stream =>
                      if _textEq : stream.text = response.body then
                        if _sourceEq : bytesOfList finalState.source = response.body.toUTF8 then
                          .ok {
                            state := finalState
                            rawChunks
                            pendingRaw := pending
                            pendingLine := none
                            status := some response.status
                            statusSeen
                            stop := .completed stream
                            rawBytes
                            raw_chunks_eq := rfl
                          }
                        else
                          .error .sourceMismatch
                      else
                        .error (.bodyMismatch response.body stream.text)

private def runBytePrefixLoop
    (policy : LinePolicy)
    (fuel chunkSize : Nat)
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String))
    (stdout : IO.FS.Stream)
    (state : BytePrefixState)
    (pending : List UInt8)
    (pendingLine : Option (List UInt8))
    (statusSeen : Bool)
    (rawChunksRev : List ByteArray) :
    IO (Except BytePrefixClientError (BytePrefixResponse policy)) :=
  match fuel with
  | 0 => do
      cleanup child stderrTask
      let rawChunks := rawChunksRev.reverse
      let rawBytes := DeepSeekCurlByteFraming.concatChunks rawChunks
      pure (.ok {
        state
        rawChunks
        pendingRaw := pending
        pendingLine
        status := none
        statusSeen
        stop := .fuelExhausted
        rawBytes
        raw_chunks_eq := rfl
      })
  | fuel + 1 => do
      if decided : policy.decide state.typed.line then
        cleanup child stderrTask
        let rawChunks := rawChunksRev.reverse
        let rawBytes := DeepSeekCurlByteFraming.concatChunks rawChunks
        pure (.ok {
          state
          rawChunks
          pendingRaw := pending
          pendingLine
          status := none
          statusSeen
          stop := .cancelled state.typed.line policy.reason decided
          rawBytes
          raw_chunks_eq := rfl
        })
      else
        try
          let chunk ← stdout.read chunkSize.toUSize
          if chunk.isEmpty then
            let exitCode ← child.wait
            let stderr ← IO.ofExcept stderrTask.get
            pure <| finishObserved policy state pending pendingLine statusSeen
              rawChunksRev.reverse
              exitCode stderr
          else
            match pushOutputChunk state pending pendingLine statusSeen chunk with
            | .error error =>
                cleanup child stderrTask
                pure (.error error)
            | .ok next =>
                runBytePrefixLoop policy fuel chunkSize child stderrTask stdout next.state
                  next.pending next.pendingLine next.statusSeen (chunk :: rawChunksRev)
        catch error =>
          cleanup child stderrTask
          pure (.error (.io (toString error)))

def executeSseBytePrefix
    (policy : LinePolicy)
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except BytePrefixClientError (BytePrefixResponse policy)) := do
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
      runBytePrefixLoop policy maxReads chunkSize child stderrTask
        (IO.FS.Stream.ofHandle child.stdout) BytePrefixState.initial [] none false []
    catch error =>
      pure (.error (.io (toString error)))

def fixtureProcess (responseBody : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-byte-prefix-fixture",
    responseBody
  ]

def fixtureResponse : IO (Except BytePrefixClientError
    (BytePrefixResponse (LinePolicy.never))) :=
  executeSseBytePrefix (LinePolicy.never) 4096 1
    (fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

def cancellationResponse : IO (Except BytePrefixClientError
    (BytePrefixResponse (LinePolicy.atLine 1 "cancelled:byte-prefix"))) :=
  executeSseBytePrefix (LinePolicy.atLine 1 "cancelled:byte-prefix") 4096 1
    (fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

end Cordis.DeepSeekCurlBytePrefix
