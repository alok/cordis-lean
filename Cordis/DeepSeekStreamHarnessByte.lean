import Cordis.DeepSeekCurlByteFraming
import Cordis.DeepSeekStreamHarness

/-!
# Byte-backed DeepSeek stream to generic Harness continuation

This module is the byte-ingress companion to `DeepSeekStreamHarness`: a bounded piped process is
read as arbitrary `ByteArray` chunks, the exact byte/framing/status witness is retained, and only
then is the decoded body passed to the existing rich-stream/session/tool continuation.  The
returned round keeps both certificates instead of erasing the process boundary to a `String`.

The adapter is deliberately finite and synchronous.  It does not claim network or credential
validity, executable trust, blocked-read interruption, backpressure, reconnects, provider-complete
assembly, or equivalence to deployed DeepSeek Harness behavior.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessByte

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlByteFraming
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

inductive ByteStreamConversationError where
  | request (error : RequestError)
  | client (error : ByteChunkError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | tool (error : ToolRoundError)
deriving DecidableEq

structure ByteStreamConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  observed : ByteChunkResponse body
  round : StreamConversationRoundResult cfg before body

def executeConversationByteStreamRound
    {Model Capability : Type}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ByteStreamConversationError
      (Sigma fun body : String => ByteStreamConversationRoundResult cfg before body)) := do
  match buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeSseBytes maxReads chunkSize config plan.request with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, observed⟩ =>
          match finish body with
          | .error error => pure (.error (.response error))
          | .ok finished =>
              let assistantSeq := runner.session.nextSeq
              let assistantRunner := ConversationRunner.appendFinished runner finished
                sourceEventSeqs sourcesNodup sourcesEarlier
              have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                rw [ConversationRunner.appendFinished_nextSeq]
                exact Nat.lt_succ_self _
              match executionEq : executeFunctionCalls cfg before
                  (finishedFunctionCalls finished) with
              | .error error => pure (.error (.tool error))
              | .ok (finalModel, executions) =>
                  let finalRunner := ConversationRunner.appendToolResults assistantRunner
                    runner.nextCall assistantSeq executions assistantSeqEarlier
                  pure (.ok ⟨body, {
                    observed
                    round := {
                      finished
                      assistantRunner
                      runner := finalRunner
                      finalModel
                      executions
                      executions_eq := executionEq
                      assistantSeq
                      assistantSeq_eq := by
                        change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                        rw [ConversationRunner.appendFinished_nextSeq]
                    }
                  }⟩)

def executeConversationMultiByteStreamRound
    {Model Capability : Type}
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ByteStreamConversationError
      (Sigma fun body : String => ByteStreamConversationRoundResult cfg before body)) :=
  executeConversationByteStreamRound finishMulti maxReads chunkSize config baseUrl apiKey source cfg
    before runner sourceEventSeqs sourcesNodup sourcesEarlier

abbrev ByteStreamConversationWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String =>
    ByteStreamConversationRoundResult cfg before body

namespace ByteStreamConversationWitness

abbrev noToolCalls
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    ByteStreamConversationWitness cfg → Prop
  | ⟨_, ⟨_, result⟩⟩ => result.round.finished.finished.view.rawToolCalls.length = 0

end ByteStreamConversationWitness

inductive ByteStreamConversationStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : ByteStreamConversationWitness cfg)
      (noToolCalls : ByteStreamConversationWitness.noToolCalls last)
  | fuelExhausted

namespace ByteStreamConversationStop

def isCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    ByteStreamConversationStop cfg → Bool
  | .completed _ _ => true
  | .fuelExhausted => false

end ByteStreamConversationStop

structure ByteStreamConversationRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (ByteStreamConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : ByteStreamConversationStop cfg

def runConversationMultiByteStreamAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (fuel : Nat)
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (ByteStreamConversationWitness cfg)) :
    IO (Except ByteStreamConversationError (ByteStreamConversationRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeConversationByteStreamRound finish maxReads chunkSize config baseUrl apiKey
          source cfg before runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : ByteStreamConversationWitness cfg := ⟨before, ⟨body, round⟩⟩
          let nextHistory := history ++ [witness]
          if noTools : ByteStreamConversationWitness.noToolCalls witness then
            pure (.ok {
              rounds := nextHistory
              runner := round.round.runner
              finalModel := round.round.finalModel
              stop := .completed witness noTools
            })
          else
            runConversationMultiByteStreamAux finish fuel maxReads chunkSize config baseUrl apiKey
              source sourceEventSeqs sourcesNodup sourcesEarlier round.round.finalModel
              round.round.runner nextHistory
termination_by fuel

def runConversationMultiByteStream
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except ByteStreamConversationError (ByteStreamConversationRunResult cfg)) :=
  runConversationMultiByteStreamAux finishMulti fuel maxReads chunkSize config baseUrl apiKey source
    sourceEventSeqs sourcesNodup sourcesEarlier before runner []

end Cordis.DeepSeekStreamHarnessByte
