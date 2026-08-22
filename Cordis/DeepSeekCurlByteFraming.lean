import Cordis.DeepSeekStreamByteFraming
import Cordis.DeepSeekCurlStream

/-!
# Process-backed byte-chunk DeepSeek SSE framing

`DeepSeekStreamByteFraming` proves the pure byte-ingress contract. This module connects that
contract to the existing piped-process boundary: stdout is read as bounded `ByteArray` chunks,
the complete process output is decoded and split at the private HTTP status trailer, and the
observed body chunks are fed unchanged to the pure byte framer. The result retains the raw chunks,
their canonical concatenation, the parsed status/body equation, and the exact byte-framed SSE
certificate.

The adapter is intentionally a finite process fixture and a bounded reader. It does not claim
network or credential validity, executable trust, blocked-read interruption, backpressure,
cancellation, reconnects, provider-complete assembly, or deployed DeepSeek Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlByteFraming

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamByteFraming

inductive ByteChunkError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | utf8 (bytes : ByteArray)
  | framing (error : ByteFramingError)
  | readLimit (reads : Nat)
  | chunkSize
  | bodyMismatch (expected : String) (actual : String)
  | bytesMismatch
  | io (message : String)
deriving DecidableEq

def concatChunks : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | chunk :: rest => chunk.append (concatChunks rest)

def clipChunks : Nat → List ByteArray → List ByteArray
  | 0, _ => []
  | _, [] => []
  | remaining, chunk :: rest =>
      let take := min remaining chunk.size
      let clipped := chunk.extract 0 take
      if remaining ≤ chunk.size then
        [clipped]
      else
        clipped :: clipChunks (remaining - chunk.size) rest

def killAndWait
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) : IO Unit := do
  try
    child.kill
  catch _ =>
    pure ()
  try
    discard <| child.wait
  catch _ =>
    pure ()

def readByteChunks
    (fuel chunkSize : Nat)
    (stdout : IO.FS.Stream)
    (chunksRev : List ByteArray) :
    IO (Except ByteChunkError (List ByteArray)) :=
  match fuel with
  | 0 => pure (.error (.readLimit chunksRev.length))
  | fuel + 1 => do
      try
        let chunk ← stdout.read chunkSize.toUSize
        if chunk.isEmpty then
          pure (.ok chunksRev.reverse)
        else
          readByteChunks fuel chunkSize stdout (chunk :: chunksRev)
      catch error =>
        pure (.error (.io (toString error)))

structure ByteChunkResponse (body : String) where
  status : Nat
  rawText : String
  rawBytes : ByteArray
  chunks : List ByteArray
  bodyChunks : List ByteArray
  rawDecoded : String.fromUTF8? rawBytes = some rawText
  parsed : parseOutput rawText = .ok { status, body }
  raw_chunks_eq : concatChunks chunks = rawBytes
  body_chunks_eq : concatChunks bodyChunks = body.toUTF8
  framed : ValidatedByteStream
  framed_text_eq : framed.text = body

def executeSseBytes
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except ByteChunkError (Sigma fun body : String => ByteChunkResponse body)) := do
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
      let observed := try
        readByteChunks maxReads chunkSize (IO.FS.Stream.ofHandle child.stdout) []
      catch error =>
        killAndWait child
        pure (.error (.io (toString error)))
      match ← observed with
      | .error error =>
          killAndWait child
          pure (.error error)
      | .ok chunks =>
          let exitCode ← child.wait
          let stderr ← IO.ofExcept stderrTask.get
          if exitCode != 0 then
            pure (.error (.process (.exited exitCode stderr)))
          else
            let rawBytes := concatChunks chunks
            match decoded : String.fromUTF8? rawBytes with
            | none => pure (.error (.utf8 rawBytes))
            | some rawText =>
                match parsed : parseOutput rawText with
                | .error error => pure (.error (.process error))
                | .ok response =>
                    if response.status < 200 || response.status ≥ 300 then
                      pure (.error (.httpStatus response.status response.body))
                    else
                      let bodyChunks := clipChunks response.body.toUTF8.size chunks
                      if bytesEq : concatChunks bodyChunks = response.body.toUTF8 then
                        match validateChunks bodyChunks with
                        | .error error => pure (.error (.framing error))
                        | .ok validated =>
                            if textEq : validated.text = response.body then
                              pure (.ok ⟨response.body, {
                                status := response.status
                                rawText
                                rawBytes
                                chunks
                                bodyChunks
                                rawDecoded := decoded
                                parsed := parsed
                                raw_chunks_eq := rfl
                                body_chunks_eq := bytesEq
                                framed := validated
                                framed_text_eq := textEq
                              }⟩)
                            else
                              pure (.error (.bodyMismatch response.body validated.text))
                      else
                        pure (.error .bytesMismatch)
    catch error =>
      pure (.error (.io (toString error)))

theorem ByteChunkResponse.validateSseBytes_exact
    {body : String} (result : ByteChunkResponse body) :
    Cordis.DeepSeekStream.validateSseBytes
        (bytesOfList result.framed.source) =
      .ok ⟨result.framed.text, result.framed.stream⟩ := by
  exact ValidatedByteStream.validateSseBytes_exact result.framed

def fixtureProcess (responseBody : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-byte-fixture",
    responseBody
  ]

def fixtureResponse : IO (Except ByteChunkError
    (Sigma fun body : String => ByteChunkResponse body)) :=
  executeSseBytes 256 3 (fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

def unicodeFixtureResponse : IO (Except ByteChunkError
    (Sigma fun body : String => ByteChunkResponse body)) :=
  executeSseBytes 256 2 (fixtureProcess DeepSeekStreamByteFraming.unicodeBody)
    DeepSeekCurlTransport.fixtureRequest.request

end Cordis.DeepSeekCurlByteFraming
