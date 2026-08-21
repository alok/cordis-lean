import Cordis.DeepSeekHarnessErrors
import Cordis.DeepSeekStreamHarness

/-!
# Recoverable provider failures in the streamed Harness

This module lifts the explicit recoverable-provider policy from
`DeepSeekHarnessErrors` through the complete-body streamed response boundary. A streamed
assistant tool call is still parsed, admitted, and policy-checked before execution. If the
provider fails, the typed `ProviderFailedTool` is retained, the model is unchanged, and an
`isError` tool result is appended to the streamed session so a caller can opt into a subsequent
request with `RequestSource.errorToolResults := .include`.

The process boundary remains complete-body. This is not a claim about incremental reads,
blocked-read cancellation, reconnects, retries, persistence, provider-complete assembly, or
equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessErrors

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessErrors
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

inductive StreamRecoverableConversationError where
  | request (error : RequestError)
  | client (error : SessionClientError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

structure StreamRecoverableRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  finished : FinishedResponse body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  attempts : List (RecoverableToolAttempt cfg)
  attempts_eq :
    executeFunctionCallsRecoverable cfg before (finishedFunctionCalls finished) =
      .ok (finalModel, attempts)
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

def executeConversationMultiStreamRoundRecoverable
    {Model Capability : Type}
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
    IO (Except StreamRecoverableConversationError
      (Sigma fun body : String => StreamRecoverableRoundResult cfg before body)) := do
  match buildRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← DeepSeekCurlSession.executeWith finishMulti config plan.request with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, processed⟩ =>
          let assistantSeq := runner.session.nextSeq
          let assistantRunner := ConversationRunner.appendFinished runner processed.finished
            sourceEventSeqs sourcesNodup sourcesEarlier
          have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
            rw [ConversationRunner.appendFinished_nextSeq]
            exact Nat.lt_succ_self _
          match attemptEq : executeFunctionCallsRecoverable cfg before
              (finishedFunctionCalls processed.finished) with
          | .error error => pure (.error (.tool error))
          | .ok (finalModel, attempts) =>
              let finalRunner := ConversationRunner.appendRecoverableToolResults assistantRunner
                runner.nextCall assistantSeq attempts assistantSeqEarlier
              pure (.ok ⟨body, {
                finished := processed.finished
                assistantRunner
                runner := finalRunner
                finalModel
                attempts
                attempts_eq := attemptEq
                assistantSeq
                assistantSeq_eq := by
                  change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                  rw [ConversationRunner.appendFinished_nextSeq]
              }⟩)

def fixtureFailureProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-stream-recoverable-fixture",
    DeepSeekStreamHarness.counterToolStreamBody
  ]

end Cordis.DeepSeekStreamHarnessErrors
