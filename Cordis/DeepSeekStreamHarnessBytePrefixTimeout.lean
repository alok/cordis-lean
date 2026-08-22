import Cordis.DeepSeekCurlBytePrefixTimeout
import Cordis.DeepSeekStreamHarnessBytePrefix

/-!
# Timed byte-prefix continuation into the streamed Harness

This module composes the timer-backed byte-prefix reader with the existing typed streamed
Harness round.  A completed byte prefix is passed through the same response validator, dependent
tool execution, and session append as the ordinary byte-prefix adapter.  A fuel, cancellation,
or timeout stop is retained as the observed prefix rather than being mistaken for a terminal
response.

The process remains caller-configured and local.  This does not claim network or credential
validity, executable trust, arbitrary descendant cleanup, fairness, backpressure, reconnects,
provider-complete assembly, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessBytePrefixTimeout

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlBytePrefixTimeout
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessBytePrefix
open Cordis.DeepSeekStreamIncremental

inductive TimedBytePrefixConversationError where
  | request (error : RequestError)
  | client (error : BytePrefixClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | tool (error : ToolRoundError)
  | prefixStop (response : TimedBytePrefixResponse (LinePolicy.never))

structure TimedBytePrefixConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  observed : TimedBytePrefixResponse (LinePolicy.never)
  round : StreamConversationRoundResult cfg before body

def executeConversationTimedBytePrefixRound
    {Model Capability : Type}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
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
    IO (Except TimedBytePrefixConversationError
      (Sigma fun body : String =>
        TimedBytePrefixConversationRoundResult cfg before body)) := do
  match buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeSseBytePrefixWithTimeout (LinePolicy.never) maxReads chunkSize timeoutMs
          config plan.request with
      | .error error => pure (.error (.client error))
      | .ok observed =>
          match observed.stop with
          | .fuelExhausted | .cancelled _ _ _ | .timedOut _ _ =>
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

def executeConversationMultiTimedBytePrefixRound
    {Model Capability : Type}
    (maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
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
    IO (Except TimedBytePrefixConversationError
      (Sigma fun body : String =>
        TimedBytePrefixConversationRoundResult cfg before body)) :=
  executeConversationTimedBytePrefixRound finishMulti maxReads chunkSize timeoutMs config baseUrl
    apiKey source cfg before runner sourceEventSeqs sourcesNodup sourcesEarlier

abbrev TimedBytePrefixConversationWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String =>
    TimedBytePrefixConversationRoundResult cfg before body

namespace TimedBytePrefixConversationWitness

abbrev noToolCalls
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    TimedBytePrefixConversationWitness cfg → Prop
  | ⟨_, ⟨_, result⟩⟩ => result.round.finished.finished.view.rawToolCalls.length = 0

end TimedBytePrefixConversationWitness

inductive TimedBytePrefixConversationStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : TimedBytePrefixConversationWitness cfg)
      (noToolCalls : TimedBytePrefixConversationWitness.noToolCalls last)
  | fuelExhausted
  | prefixStopped (response : TimedBytePrefixResponse (LinePolicy.never))

namespace TimedBytePrefixConversationStop

def isCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    TimedBytePrefixConversationStop cfg → Bool
  | .completed _ _ => true
  | .fuelExhausted | .prefixStopped _ => false

end TimedBytePrefixConversationStop

structure TimedBytePrefixConversationRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (TimedBytePrefixConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : TimedBytePrefixConversationStop cfg

def runConversationMultiTimedBytePrefixAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (fuel : Nat)
    (maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
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
    (history : List (TimedBytePrefixConversationWitness cfg)) :
    IO (Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeConversationTimedBytePrefixRound finish maxReads chunkSize timeoutMs config
          baseUrl apiKey source cfg before runner sourceEventSeqs sourcesNodup
          (sourcesEarlier runner) with
      | .error (.prefixStop response) =>
          pure (.ok {
            rounds := history
            runner
            finalModel := before
            stop := .prefixStopped response
          })
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : TimedBytePrefixConversationWitness cfg := ⟨before, ⟨body, round⟩⟩
          let nextHistory := history ++ [witness]
          if noTools : TimedBytePrefixConversationWitness.noToolCalls witness then
            pure (.ok {
              rounds := nextHistory
              runner := round.round.runner
              finalModel := round.round.finalModel
              stop := .completed witness noTools
            })
          else
            runConversationMultiTimedBytePrefixAux finish fuel maxReads chunkSize timeoutMs config
              baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
              round.round.finalModel round.round.runner nextHistory
termination_by fuel

def runConversationMultiTimedBytePrefix
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
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
    IO (Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult cfg)) :=
  runConversationMultiTimedBytePrefixAux finishMulti fuel maxReads chunkSize timeoutMs config
    baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier before runner []

namespace Example

theorem timeout_stop_is_not_completed
    {policy : LinePolicy}
    (response : TimedBytePrefixResponse policy)
    {line : Nat} {timeoutMs : UInt32}
    (stop_eq : response.stop = .timedOut line timeoutMs) :
    response.isCompleted = false := by
  change BytePrefixTimeoutStop.isCompleted response.stop = false
  rw [stop_eq]
  rfl

theorem timeout_stop_preserves_prefix_line
    {policy : LinePolicy}
    (response : TimedBytePrefixResponse policy)
    {line : Nat} {timeoutMs : UInt32}
    (stop_eq : response.stop = .timedOut line timeoutMs) :
    line = response.state.typed.line :=
  response.timeout_line_eq_prefix stop_eq

end Example

end Cordis.DeepSeekStreamHarnessBytePrefixTimeout
