import Cordis.DeepSeekCurlBytePrefix
import Cordis.DeepSeekStreamHarnessByte

/-!
# Process-byte prefix to generic Harness continuation

This module composes the bounded process-byte prefix reader with the existing rich/tool/session
continuation. A completed prefix carries a dependent strict SSE certificate, and only that
certificate's decoded body is passed to the same assistant append, dependent tool execution, and
certified tool-result append used by the complete-body Harness adapter. A prefix fuel stop is kept
as a typed Harness stop rather than being mistaken for a terminal response.

The adapter remains a finite process boundary. It does not claim network or credential validity,
executable trust, blocked-read interruption, backpressure, reconnects, provider-complete assembly,
or equivalence to a deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessBytePrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessByte
open Cordis.DeepSeekStreamIncremental

inductive BytePrefixConversationError where
  | request (error : RequestError)
  | client (error : BytePrefixClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | tool (error : ToolRoundError)
  | prefixStop (response : BytePrefixResponse (LinePolicy.never))

structure BytePrefixConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  observed : BytePrefixResponse (LinePolicy.never)
  round : StreamConversationRoundResult cfg before body

def executeConversationBytePrefixRound
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
    IO (Except BytePrefixConversationError
      (Sigma fun body : String =>
        BytePrefixConversationRoundResult cfg before body)) := do
  match buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeSseBytePrefix (LinePolicy.never) maxReads chunkSize config plan.request with
      | .error error => pure (.error (.client error))
      | .ok observed =>
          match observed.stop with
          | .fuelExhausted | .cancelled _ _ _ =>
              pure (.error (.prefixStop observed))
          | .completed stream =>
              let body := stream.text
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

def executeConversationMultiBytePrefixRound
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
    IO (Except BytePrefixConversationError
      (Sigma fun body : String =>
        BytePrefixConversationRoundResult cfg before body)) :=
  executeConversationBytePrefixRound finishMulti maxReads chunkSize config baseUrl apiKey source cfg
    before runner sourceEventSeqs sourcesNodup sourcesEarlier

abbrev BytePrefixConversationWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String =>
    BytePrefixConversationRoundResult cfg before body

namespace BytePrefixConversationWitness

abbrev noToolCalls
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    BytePrefixConversationWitness cfg → Prop
  | ⟨_, ⟨_, result⟩⟩ => result.round.finished.finished.view.rawToolCalls.length = 0

end BytePrefixConversationWitness

inductive BytePrefixConversationStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : BytePrefixConversationWitness cfg)
      (noToolCalls : BytePrefixConversationWitness.noToolCalls last)
  | fuelExhausted
  | prefixStopped (response : BytePrefixResponse (LinePolicy.never))

namespace BytePrefixConversationStop

def isCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    BytePrefixConversationStop cfg → Bool
  | .completed _ _ => true
  | .fuelExhausted | .prefixStopped _ => false

end BytePrefixConversationStop

structure BytePrefixConversationRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (BytePrefixConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : BytePrefixConversationStop cfg

def runConversationMultiBytePrefixAux
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
    (history : List (BytePrefixConversationWitness cfg)) :
    IO (Except BytePrefixConversationError (BytePrefixConversationRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeConversationBytePrefixRound finish maxReads chunkSize config baseUrl apiKey
          source cfg before runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error (.prefixStop response) =>
          pure (.ok {
            rounds := history
            runner
            finalModel := before
            stop := .prefixStopped response
          })
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : BytePrefixConversationWitness cfg := ⟨before, ⟨body, round⟩⟩
          let nextHistory := history ++ [witness]
          if noTools : BytePrefixConversationWitness.noToolCalls witness then
            pure (.ok {
              rounds := nextHistory
              runner := round.round.runner
              finalModel := round.round.finalModel
              stop := .completed witness noTools
            })
          else
            runConversationMultiBytePrefixAux finish fuel maxReads chunkSize config baseUrl apiKey
              source sourceEventSeqs sourcesNodup sourcesEarlier round.round.finalModel
              round.round.runner nextHistory
termination_by fuel

def runConversationMultiBytePrefix
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
    IO (Except BytePrefixConversationError (BytePrefixConversationRunResult cfg)) :=
  runConversationMultiBytePrefixAux finishMulti fuel maxReads chunkSize config baseUrl apiKey source
    sourceEventSeqs sourcesNodup sourcesEarlier before runner []

end Cordis.DeepSeekStreamHarnessBytePrefix
