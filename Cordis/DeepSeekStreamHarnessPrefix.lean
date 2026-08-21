import Cordis.DeepSeekCurlPrefix
import Cordis.DeepSeekHarness
import Cordis.DeepSeekStreamHarness

/-!
# Line-prefix DeepSeek stream to generic harness continuation

This module connects the proof-carrying process prefix boundary to the streamed generic harness
round. Complete response lines are parsed before the next process read; a completed prefix then
uses the same multi-call rich/session/tool continuation as `DeepSeekStreamHarness`. If the line
policy or read budget stops first, the exact prefix and typed stop are returned instead of being
collapsed into a generic client error.

The boundary is intentionally line-oriented. It does not claim interruption of a blocked read,
byte framing, backpressure, reconnects, provider-complete assembly, external tool cancellation,
or equivalence to deployed DeepSeek Harness behavior.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessPrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental

inductive PrefixStreamConversationError where
  | request (error : RequestError)
  | client (error : PrefixClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

inductive PrefixStreamRoundOutcome
    {Model Capability : Type}
    (policy : LinePolicy)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  | completed {body : String}
      (observed : PrefixResponse policy)
      (body_eq : observed.state.body = body)
      (round : StreamConversationRoundResult cfg before body)
  | fuelExhausted (observed : PrefixResponse policy)
  | cancelled
      (observed : PrefixResponse policy)
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true)

namespace PrefixStreamRoundOutcome

def isCompleted
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} :
    PrefixStreamRoundOutcome policy cfg before → Bool
  | .completed _ _ _ => true
  | .fuelExhausted _ | .cancelled _ _ _ _ => false

def isFuelExhausted
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} :
    PrefixStreamRoundOutcome policy cfg before → Bool
  | .completed _ _ _ | .cancelled _ _ _ _ => false
  | .fuelExhausted _ => true

def isCancelled
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} :
    PrefixStreamRoundOutcome policy cfg before → Bool
  | .completed _ _ _ | .fuelExhausted _ => false
  | .cancelled _ _ _ _ => true

def cancelledLine
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} :
    PrefixStreamRoundOutcome policy cfg before → Option Nat
  | .completed _ _ _ | .fuelExhausted _ => none
  | .cancelled _ line _ _ => some line

def cancelledReason
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} :
    PrefixStreamRoundOutcome policy cfg before → Option String
  | .completed _ _ _ | .fuelExhausted _ => none
  | .cancelled _ _ reason _ => some reason

end PrefixStreamRoundOutcome

def executeConversationMultiStreamPrefixRound
    {Model Capability : Type}
    (policy : LinePolicy)
    (maxReads : Nat)
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
    IO (Except PrefixStreamConversationError (PrefixStreamRoundOutcome policy cfg before)) := do
  match buildRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeSsePrefix policy maxReads config plan.request with
      | .error error => pure (.error (.client error))
      | .ok observed =>
          match observed.stop with
          | .fuelExhausted => pure (.ok (.fuelExhausted observed))
          | .cancelled line reason decided =>
              pure (.ok (.cancelled observed line reason decided))
          | .completed _ =>
              match finishMulti observed.state.body with
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
                      pure (.ok (.completed observed rfl {
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
                      }))

def fixtureMultiProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "body=$(cat); case \"$body\" in " ++
      "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
      "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
    "cordis-prefix-stream-harness-fixture",
    DeepSeekStreamHarness.counterMultiToolStreamBody,
    DeepSeekRichStream.exampleTextStreamBody
  ]

end Cordis.DeepSeekStreamHarnessPrefix
