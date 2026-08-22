import Cordis.DeepSeekProviderStreamAssembly

/-!
# Incremental provider assembly prefix

The source-shaped provider assembler is a state transition over canonical chunks.  This module
keeps that transition visible while rich raw chunks arrive one at a time: every accepted prefix
retains the raw chunks, mapped chunks, and exact `pushMany` state equation.  `finish` is separate
and only succeeds when the current assembler state can be assembled.

This is a pure prefix model.  It does not claim live transport, byte framing, cancellation,
backpressure, persistence, or deployed TypeScript equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProviderAssemblyPrefix

open Cordis
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.RichStream

theorem mapRawChunks_append (left right : List RawChunk) :
    mapRawChunks (left ++ right) = (do
      let mappedLeft ← mapRawChunks left
      let mappedRight ← mapRawChunks right
      pure (mappedLeft ++ mappedRight)) := by
  induction left with
  | nil =>
      rw [List.nil_append]
      simp only [mapRawChunks]
      cases hRight : mapRawChunks right with
      | error e => rfl
      | ok ys => rfl
  | cons head tail inductionHypothesis =>
      rw [List.cons_append]
      simp only [mapRawChunks]
      cases hHead : mapRawChunk head with
      | error e => rfl
      | ok x =>
          cases hTail : mapRawChunks tail with
          | error e =>
              rw [inductionHypothesis, hTail]
              rfl
          | ok xs =>
              cases hRight : mapRawChunks right with
              | error e =>
                  rw [inductionHypothesis, hTail, hRight]
                  rfl
              | ok ys =>
                  rw [inductionHypothesis, hTail, hRight]
                  rfl

structure PrefixState where
  raw : List RawChunk
  chunks : List Chunk
  state : Cordis.DeepSeekProviderAssembler.State
  chunks_eq : mapRawChunks raw = .ok chunks
  state_eq : pushMany chunks = state

def initial : PrefixState where
  raw := []
  chunks := []
  state := Cordis.DeepSeekProviderAssembler.initial
  chunks_eq := rfl
  state_eq := rfl

def pushRaw (acc : PrefixState) (raw : RawChunk) :
    Except ProviderStreamError PrefixState :=
  match mapped : mapRawChunk raw with
  | .error error => .error error
  | .ok chunk =>
      let nextRaw := acc.raw ++ [raw]
      let nextChunks := acc.chunks ++ [chunk]
      .ok {
        raw := nextRaw
        chunks := nextChunks
        state := push acc.state chunk
        chunks_eq := by
          rw [mapRawChunks_append, acc.chunks_eq]
          simp only [mapRawChunks]
          rw [mapped]
          rfl
        state_eq := by
          rw [pushMany, List.foldl_append]
          change push (pushMany acc.chunks) chunk = push acc.state chunk
          rw [acc.state_eq]
      }

def pushAll (acc : PrefixState) : List RawChunk →
    Except ProviderStreamError PrefixState
  | [] => .ok acc
  | raw :: rest => do
      let next ← pushRaw acc raw
      pushAll next rest

def finish (acc : PrefixState) : Except AssemblyError (Certificate acc.chunks) :=
  match resultEq : assemble acc.state with
  | .error error => .error error
  | .ok result => .ok {
      state := acc.state
      state_eq := acc.state_eq
      result
      result_eq := resultEq
    }

theorem PrefixState.chunks_exact (acc : PrefixState) :
    mapRawChunks acc.raw = .ok acc.chunks :=
  acc.chunks_eq

theorem PrefixState.state_exact (acc : PrefixState) :
    pushMany acc.chunks = acc.state :=
  acc.state_eq

theorem finish_exact {acc : PrefixState} {certificate : Certificate acc.chunks}
    (hFinish : finish acc = .ok certificate) :
    assemble acc.state = .ok certificate.result := by
  unfold finish at hFinish
  split at hFinish
  · cases hFinish
  · cases hFinish
    assumption

def counterPrefix : Except ProviderStreamError PrefixState :=
  match validateBody counterBody with
  | .error error => .error error
  | .ok validated => pushAll initial validated.source.raw

def counterPrefixSummary : Bool :=
  match counterPrefix with
  | .error _ => false
  | .ok acc =>
      match finish acc with
      | .error _ => false
      | .ok certificate =>
          certificate.result.blocks == [
            .toolCall "counter-call-0" "counter_increment" "[3,10]"
          ] && certificate.result.finish == .toolCalls && acc.raw.length == 6

end Cordis.DeepSeekProviderAssemblyPrefix
