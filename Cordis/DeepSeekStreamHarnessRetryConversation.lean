import Cordis.DeepSeekStreamHarnessRetry

/-!
# Process-backed retry-aware streamed conversation

This module composes the complete-body streamed retry boundary with the indexed conversation
loop.  Each trace head retains the accepted SSE body, retry history, streamed assistant/tool
endpoint, and exact final runner/model; the tail is indexed by that endpoint.  Completion and
fuel exhaustion are distinct, while request/process/response/tool failures remain typed.

The boundary is intentionally local: it does not establish backoff, idempotency, cancellation of
blocked reads, persistence, reconnect semantics, arbitrary external effects, live credentials,
or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry

/-! ## Indexed streamed retry rounds and traces -/

structure StreamRetryRoundBox
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model) where
  body : String
  round : ConversationRoundResult policy cfg before body

namespace StreamRetryRoundBox

def noToolCalls
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner : ConversationRunner} {before : Model}
    (box : StreamRetryRoundBox policy cfg config baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier runner before) : Prop :=
  box.round.round.finished.finished.view.rawToolCalls.length = 0

end StreamRetryRoundBox

inductive StreamRetryTrace
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    ConversationRunner → Model → ConversationRunner → Model → Type where
  | nil
      (runner : ConversationRunner)
      (before : Model) :
      StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before runner before
  | cons
      {runner : ConversationRunner}
      {before : Model}
      {finalRunner : ConversationRunner}
      {finalModel : Model}
      (head : StreamRetryRoundBox policy cfg config baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (tail : StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier head.round.round.runner head.round.round.finalModel
        finalRunner finalModel) :
      StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before finalRunner finalModel

namespace StreamRetryTrace

def length
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model} :
    StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons _ tail => Nat.succ tail.length

theorem length_cons
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model}
    (head : StreamRetryRoundBox policy cfg config baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier runner before)
    (tail : StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier head.round.round.runner head.round.round.finalModel finalRunner
      finalModel) :
    length (.cons head tail) = Nat.succ (length tail) :=
  rfl

end StreamRetryTrace

/-! ## Typed stops and run result -/

inductive StreamRetryStop
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      (last : StreamRetryRoundBox policy cfg config baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (runner_eq : last.round.round.runner = finalRunner)
      (model_eq : last.round.round.finalModel = finalModel)
      (noToolCalls : StreamRetryRoundBox.noToolCalls last)
  | fuelExhausted

namespace StreamRetryStop

def isCompleted
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    StreamRetryStop policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => true
  | .fuelExhausted => false

def isFuelExhausted
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    StreamRetryStop policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => false
  | .fuelExhausted => true

end StreamRetryStop

structure StreamRetryConversationRunResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (initialRunner : ConversationRunner)
    (initialModel : Model)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  trace : StreamRetryTrace policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier initialRunner initialModel finalRunner finalModel
  stop : StreamRetryStop policy cfg config baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier finalRunner finalModel

/-! ## Process-backed retry-aware loop -/

def runAux
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
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
    IO (Except (ConversationError policy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          StreamRetryConversationRunResult policy cfg config baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      match ← executeConversationMultiStreamRound policy config baseUrl apiKey source cfg before
          runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let head : StreamRetryRoundBox policy cfg config baseUrl apiKey source sourceEventSeqs
              sourcesNodup sourcesEarlier runner before := { body, round }
          let callCount := head.round.round.finished.finished.view.rawToolCalls.length
          if noTools : callCount = 0 then
            pure (.ok ⟨round.round.runner, ⟨round.round.finalModel, {
              trace := .cons head (.nil round.round.runner round.round.finalModel)
              stop := .completed head rfl rfl noTools
            }⟩⟩)
          else
            match ← runAux fuel config baseUrl apiKey source sourceEventSeqs sourcesNodup
                sourcesEarlier round.round.finalModel round.round.runner with
            | .error error => pure (.error error)
            | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                pure (.ok ⟨finalRunner, ⟨finalModel, {
                  trace := .cons head tail.trace
                  stop := tail.stop
                }⟩⟩)
termination_by fuel
decreasing_by omega

def run
    {Model Capability : Type}
    {policy : RetryPolicy}
    (fuel : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (ConversationError policy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          StreamRetryConversationRunResult policy cfg config baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) :=
  runAux fuel config baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier before runner

/-! ## Executable process fixtures -/

namespace Example

def loopProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "body=$(cat); case \"$body\" in " ++
      "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
      "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
    "cordis-stream-retry-loop-fixture",
    DeepSeekStreamHarness.counterMultiToolStreamBody,
    DeepSeekRichStream.exampleTextStreamBody
  ]

def failingProcess : ProcessConfig :=
  DeepSeekStreamHarnessRetry.fixtureTransientHttpProcess DeepSeekStreamHarness.counterToolStreamBody

def counterRunner : ConversationRunner := {
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl
}

def loop : IO (Except (ConversationError DeepSeekStreamHarnessRetry.RetryPolicy.default)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Nat =>
        StreamRetryConversationRunResult DeepSeekStreamHarnessRetry.RetryPolicy.default
          Cordis.Harness.counterConfig loopProcess "https://fixture.invalid"
          { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by
            intro current source sourceMem
            cases sourceMem)
          counterRunner 0 finalRunner finalModel)) :=
  run (policy := DeepSeekStreamHarnessRetry.RetryPolicy.default) 2 loopProcess
    "https://fixture.invalid" { value := "fixture-key" } DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig [] (by simp) (by
      intro current source sourceMem
      cases sourceMem)
    0 counterRunner

def failure : IO (Except (ConversationError DeepSeekStreamHarnessRetry.RetryPolicy.default)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Nat =>
        StreamRetryConversationRunResult DeepSeekStreamHarnessRetry.RetryPolicy.default
          Cordis.Harness.counterConfig failingProcess "https://fixture.invalid"
          { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by
            intro current source sourceMem
            cases sourceMem)
          counterRunner 0 finalRunner finalModel)) :=
  run (policy := DeepSeekStreamHarnessRetry.RetryPolicy.default) 1 failingProcess
    "https://fixture.invalid" { value := "fixture-key" } DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig [] (by simp) (by
      intro current source sourceMem
      cases sourceMem)
    0 counterRunner

end Example

end Cordis.DeepSeekStreamHarnessRetryConversation
