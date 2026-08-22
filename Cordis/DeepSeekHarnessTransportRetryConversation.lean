import Cordis.DeepSeekHarnessTransportRetry

/-!
# Retry-aware, fuel-bounded Harness conversation

This module composes the proof-carrying retry round into an indexed multi-round trace. Each head
retains its complete typed request/response/tool endpoint together with the ordered retry history;
the tail is indexed by that exact final runner and model. Completion and fuel exhaustion remain
distinct typed stops.

The boundary is still an immediate retry policy over an injected complete-body transport. It does
not establish provider backoff or idempotency, cancellation of an in-flight request, persistence,
external effect correctness, live-provider behavior, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessRetry
open Cordis.DeepSeekHarnessTransportRetry

/-! ## Indexed retry rounds and traces -/

structure RetryTransportRoundBox
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model) where
  plan : TypedRequestPlan .complete
  body : String
  round : RetriedTransportRound policy baseUrl apiKey source runner plan
    (sourceEventSeqs := sourceEventSeqs)
    (sourcesNodup := sourcesNodup)
    (sourcesEarlier := sourcesEarlier runner) body cfg before

namespace RetryTransportRoundBox

def noToolCalls
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner : ConversationRunner} {before : Model}
    (box : RetryTransportRoundBox policy cfg baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier runner before) : Prop :=
  box.round.round.accepted.validated.response.choices.head.message.toolCalls.length = 0

end RetryTransportRoundBox

inductive RetryTransportTrace
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
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
      RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before runner before
  | cons
      {runner : ConversationRunner}
      {before : Model}
      {finalRunner : ConversationRunner}
      {finalModel : Model}
      (head : RetryTransportRoundBox policy cfg baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (tail : RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier head.round.round.finalRunner head.round.round.finalModel finalRunner
        finalModel) :
      RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before finalRunner finalModel

namespace RetryTransportTrace

def length
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model} :
    RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons _ tail => Nat.succ tail.length

theorem length_cons
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model}
    (head : RetryTransportRoundBox policy cfg baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier runner before)
    (tail : RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier head.round.round.finalRunner head.round.round.finalModel finalRunner
      finalModel) :
    length (.cons head tail) = Nat.succ (length tail) :=
  rfl

end RetryTransportTrace

/-! ## Completion and bounded-stop evidence -/

inductive RetryTransportStop
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
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
      (last : RetryTransportRoundBox policy cfg baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (runner_eq : last.round.round.finalRunner = finalRunner)
      (model_eq : last.round.round.finalModel = finalModel)
      (noToolCalls : RetryTransportRoundBox.noToolCalls last)
  | fuelExhausted

namespace RetryTransportStop

def isCompleted
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryTransportStop policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => true
  | .fuelExhausted => false

def isFuelExhausted
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryTransportStop policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => false
  | .fuelExhausted => true

end RetryTransportStop

structure RetryTransportConversationRunResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
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
  trace : RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier initialRunner initialModel finalRunner finalModel
  stop : RetryTransportStop policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier finalRunner finalModel

/-! ## Retry-aware fuel-bounded execution -/

def runTransportAux
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (RetryRoundError policy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryTransportConversationRunResult policy cfg baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      match ← DeepSeekHarnessTransportRetry.executeSource policy transport baseUrl apiKey source
          cfg before runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨plan, ⟨body, round⟩⟩ =>
          let head : RetryTransportRoundBox policy cfg baseUrl apiKey source sourceEventSeqs
              sourcesNodup sourcesEarlier runner before := { plan, body, round }
          let callCount :=
            head.round.round.accepted.validated.response.choices.head.message.toolCalls.length
          if noTools : callCount = 0 then
            pure (.ok ⟨round.round.finalRunner, ⟨round.round.finalModel, {
              trace := .cons head (.nil round.round.finalRunner round.round.finalModel)
              stop := .completed head rfl rfl noTools
            }⟩⟩)
          else
            match ← runTransportAux fuel transport baseUrl apiKey source sourceEventSeqs
                sourcesNodup sourcesEarlier round.round.finalModel round.round.finalRunner with
            | .error error => pure (.error error)
            | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                pure (.ok ⟨finalRunner, ⟨finalModel, {
                  trace := .cons head tail.trace
                  stop := tail.stop
                }⟩⟩)

def runTransport
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (RetryRoundError policy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryTransportConversationRunResult policy cfg baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) :=
  runTransportAux fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier before runner

/-! ## Executable retry-aware conversation fixture -/

namespace Example

def retryConversationPolicy : RetryPolicy where
  maxRetries := 1
  retryTransport := true
  retryTransientHttp := true

def retryConversationTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := if index = 0 then 503 else 200
      body := if index = 0 then "busy"
        else if index = 1 then DeepSeekHarness.counterResponseBody
        else DeepSeekHarness.counterFinalResponseBody
    })

def retryConversation :
    IO (Except (RetryRoundError retryConversationPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryTransportConversationRunResult retryConversationPolicy Cordis.Harness.counterConfig
            "https://fixture.invalid" { value := "fixture-key" }
            DeepSeekHarness.counterRequestSource [] (by simp) (by simp)
            (ConversationRunner.empty 1) 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  runTransport (policy := retryConversationPolicy) 2 (retryConversationTransport calls)
    "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource [] (by simp) (by simp) 0
    (ConversationRunner.empty 1)

end Example

end Cordis.DeepSeekHarnessTransportRetryConversation
