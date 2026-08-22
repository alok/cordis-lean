import Cordis.DeepSeekStream
import Cordis.DeepSeekStreamIncremental

/-!
# Incremental byte-level DeepSeek SSE framing

`DeepSeekStreamIncremental` accepts complete text lines. This module adds the missing pure byte
ingress: arbitrary `ByteArray` chunks are accumulated, LF-delimited byte lines are retained,
UTF-8 is decoded only after a complete line arrives, and the decoded line is fed to the existing
typed prefix state. The state carries an exact list-level reconstruction equation, so chunking is
not an erased implementation detail. `finish` requires a complete line boundary, checks that the
incremental text agrees with the complete UTF-8 source, and then invokes the strict `[DONE]`
validator.

This is still a pure framing/parser certificate. It does not claim byte-level process IO,
backpressure, blocked-read interruption, reconnects, provider-complete assembly, or deployed
DeepSeek Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamByteFraming

open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamIncremental

/-! ## Exact byte splitter -/

def isLineFeed (byte : UInt8) : Bool := byte = 10

structure SplitAccumulator where
  linesRev : List (List UInt8)
  currentRev : List UInt8

def splitStep (acc : SplitAccumulator) (byte : UInt8) : SplitAccumulator :=
  if isLineFeed byte then
    { linesRev := acc.currentRev.reverse :: acc.linesRev, currentRev := [] }
  else
    { acc with currentRev := byte :: acc.currentRev }

def splitComplete (bytes : List UInt8) : List (List UInt8) × List UInt8 :=
  let acc := bytes.foldl splitStep { linesRev := [], currentRev := [] }
  (acc.linesRev.reverse, acc.currentRev.reverse)

def reassemble : List (List UInt8) → List UInt8 → List UInt8
  | [], pending => pending
  | line :: rest, pending => line ++ [10] ++ reassemble rest pending

theorem reassemble_append_pending
    (lines : List (List UInt8)) (pending suffix : List UInt8) :
    reassemble lines (pending ++ suffix) = reassemble lines pending ++ suffix := by
  induction lines with
  | nil => simp [reassemble]
  | cons line rest ih =>
      simp only [reassemble]
      rw [ih]
      simp [List.append_assoc]

theorem reassemble_append_line
    (lines : List (List UInt8)) (line pending : List UInt8) :
    reassemble (lines ++ [line]) pending =
      reassemble lines (line ++ [10] ++ pending) := by
  induction lines with
  | nil => simp [reassemble]
  | cons head rest ih =>
      simp only [List.cons_append, reassemble]
      rw [ih]

theorem reassemble_append_lines
    (lines rest : List (List UInt8)) (pending : List UInt8) :
    reassemble (lines ++ rest) pending = reassemble lines (reassemble rest pending) := by
  induction lines with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, reassemble]
      rw [ih]

theorem splitStep_spec (acc : SplitAccumulator) (byte : UInt8) :
    reassemble acc.linesRev.reverse acc.currentRev.reverse ++ [byte] =
      reassemble (splitStep acc byte).linesRev.reverse
        (splitStep acc byte).currentRev.reverse := by
  by_cases h : byte = 10
  · have hstep : splitStep acc byte =
        { linesRev := acc.currentRev.reverse :: acc.linesRev, currentRev := [] } := by
      simp [splitStep, isLineFeed, h]
    rw [hstep]
    simp only [List.reverse_nil, List.reverse_cons]
    simp [h]
    rw [reassemble_append_line]
    simp only [List.append_nil]
    exact (reassemble_append_pending _ _ _).symm
  · have hstep : splitStep acc byte =
        { linesRev := acc.linesRev, currentRev := byte :: acc.currentRev } := by
      simp [splitStep, isLineFeed, h]
    rw [hstep]
    simp only [List.reverse_cons]
    rw [reassemble_append_pending]

theorem split_fold_spec (bytes : List UInt8) (acc : SplitAccumulator) :
    reassemble (List.foldl splitStep acc bytes).linesRev.reverse
        (List.foldl splitStep acc bytes).currentRev.reverse =
      reassemble acc.linesRev.reverse acc.currentRev.reverse ++ bytes := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte rest ih =>
      simp only [List.foldl]
      rw [ih]
      rw [← splitStep_spec]
      simp [List.append_assoc]

theorem splitComplete_spec (bytes : List UInt8) :
    let result := splitComplete bytes
    reassemble result.1 result.2 = bytes := by
  simp only [splitComplete]
  rw [split_fold_spec]
  simp [reassemble]

/-! ## Typed byte-prefix state -/

def bytesOfList (bytes : List UInt8) : ByteArray := ByteArray.mk bytes.toArray

inductive ByteFramingError where
  | invalidUtf8 (line : Nat) (bytes : ByteArray)
  | stream (line : Nat) (error : StreamError)
  | incomplete (bytes : ByteArray)
  | prefixMismatch (source : String) (prefixText : String)
deriving DecidableEq

def pushDecodedLines (lineNo : Nat) (typed : PrefixState) :
    List (List UInt8) → Except ByteFramingError PrefixState
  | [] => .ok typed
  | bytes :: rest =>
      match String.fromUTF8? (bytesOfList bytes) with
      | none => .error (.invalidUtf8 lineNo (bytesOfList bytes))
      | some text =>
          match pushLine typed text with
          | .error error => .error (.stream lineNo error)
          | .ok next => pushDecodedLines (lineNo + 1) next rest

structure BytePrefixState where
  source : List UInt8
  lines : List (List UInt8)
  pending : List UInt8
  typed : PrefixState
  framed : reassemble lines pending = source

def BytePrefixState.initial : BytePrefixState where
  source := []
  lines := []
  pending := []
  typed := PrefixState.initial
  framed := rfl

def pushChunk (state : BytePrefixState) (chunk : ByteArray) :
    Except ByteFramingError BytePrefixState :=
  let split := splitComplete (state.pending ++ chunk.toList)
  let newLines := split.1
  let pending := split.2
  match pushDecodedLines state.typed.line state.typed newLines with
  | .error error => .error error
  | .ok typed =>
      .ok {
        source := state.source ++ chunk.toList
        lines := state.lines ++ newLines
        pending
        typed
        framed := by
          calc
            reassemble (state.lines ++ newLines) pending =
                reassemble state.lines (reassemble newLines pending) :=
              reassemble_append_lines state.lines newLines pending
            _ = reassemble state.lines (state.pending ++ chunk.toList) := by
              have hsplit := splitComplete_spec (state.pending ++ chunk.toList)
              simpa [split, newLines, pending] using
                congrArg (fun bytes => reassemble state.lines bytes) hsplit
            _ = reassemble state.lines state.pending ++ chunk.toList :=
              reassemble_append_pending state.lines state.pending chunk.toList
            _ = state.source ++ chunk.toList := by rw [state.framed]
      }

theorem pushChunk_source
    (state : BytePrefixState) (chunk : ByteArray) (next : BytePrefixState)
    (pushed : pushChunk state chunk = .ok next) :
    next.source = state.source ++ chunk.toList := by
  unfold pushChunk at pushed
  dsimp only at pushed
  split at pushed
  · simp_all
  · cases pushed
    rfl

theorem pushChunk_framed
    (state : BytePrefixState) (chunk : ByteArray) (next : BytePrefixState)
    (_pushed : pushChunk state chunk = .ok next) :
    reassemble next.lines next.pending = next.source := by
  exact next.framed

/-! ## Completion and chunk runners -/

structure ValidatedByteStream where
  source : List UInt8
  text : String
  state : BytePrefixState
  decoded : String.fromUTF8? (bytesOfList source) = some text
  body_eq : state.typed.body = text
  stream : ValidatedSseStream text
  stream_validated : validateSse text = .ok stream
  pending_empty : state.pending = []

def finish (state : BytePrefixState) :
    Except ByteFramingError ValidatedByteStream :=
  if pending : state.pending = [] then
    match decoded : String.fromUTF8? (bytesOfList state.source) with
    | none => .error (.invalidUtf8 state.typed.line (bytesOfList state.source))
    | some text =>
        if body : state.typed.body = text then
          match validated : validateSse text with
          | .error error => .error (.stream state.typed.line error)
          | .ok stream => .ok {
              source := state.source
              text
              state
              decoded
              body_eq := body
              stream
              stream_validated := validated
              pending_empty := pending
            }
        else
          .error (.prefixMismatch text state.typed.body)
  else
    .error (.incomplete (bytesOfList state.pending))

def consumeChunks : BytePrefixState → List ByteArray →
    Except ByteFramingError BytePrefixState
  | state, [] => .ok state
  | state, chunk :: rest =>
      match pushChunk state chunk with
      | .error error => .error error
      | .ok next => consumeChunks next rest

def validateChunks (chunks : List ByteArray) :
    Except ByteFramingError ValidatedByteStream := do
  finish (← consumeChunks BytePrefixState.initial chunks)

theorem ValidatedByteStream.validateSseBytes_exact
    (result : ValidatedByteStream) :
    Cordis.DeepSeekStream.validateSseBytes (bytesOfList result.source) =
      .ok ⟨result.text, result.stream⟩ := by
  simp [Cordis.DeepSeekStream.validateSseBytes, result.decoded, result.stream_validated]

/-! ## Deterministic byte-chunk fixtures -/

def exampleBytes : ByteArray := (Cordis.DeepSeekStream.exampleStreamBody).toUTF8

def exampleChunks : List ByteArray := [
  exampleBytes.extract 0 2,
  exampleBytes.extract 2 7,
  exampleBytes.extract 7 19,
  exampleBytes.extract 19 exampleBytes.size
]

def exampleRuntime : Bool :=
  match validateChunks exampleChunks with
  | .ok result => result.stream.frames.length == 2 && result.state.pending.isEmpty
  | .error _ => false

def unicodeChunkJson : Lean.Json := .mkObj [
  ("id", .str "unicode-stream"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "hé")
    ]),
    ("finish_reason", .null)
  ]])
]

def unicodeBody : String :=
  "data: " ++ Lean.Json.compress unicodeChunkJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def singletonChunks (source : ByteArray) : List ByteArray :=
  source.toList.map (fun byte => ByteArray.mk #[byte])

def unicodeRuntime : Bool :=
  match validateChunks (singletonChunks unicodeBody.toUTF8) with
  | .ok result => result.stream.frames.length == 2 && result.state.pending.isEmpty
  | .error _ => false

end Cordis.DeepSeekStreamByteFraming
