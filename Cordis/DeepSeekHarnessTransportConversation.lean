import Cordis.DeepSeekHarnessPersistenceTransportRound

/-!
# Single-decoder, fuel-bounded Harness conversation

This module composes `ConversationTransportToolRound` into a dependent multi-round trace.  Every
trace cons stores the typed request plan, response body, validated/accepted response certificate,
assistant endpoint, tool executions, and final runner/model endpoint for that round.  The tail is
indexed by the preceding round's endpoint, so a trace cannot silently continue from a different
session or model.

The loop is intentionally bounded and transport-injected.  It does not claim live network or
credential validity, provider obedience, retries, cancellation, durability/fsync, external effect
correctness, or equivalence to a deployed TypeScript Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceTransportRound

/-! ## Indexed round boxes and traces -/

structure TransportRoundBox
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
  round : ConversationTransportToolRound baseUrl apiKey source runner plan
    (sourceEventSeqs := sourceEventSeqs)
    (sourcesNodup := sourcesNodup)
    (sourcesEarlier := sourcesEarlier runner) body cfg before

namespace TransportRoundBox

def noToolCalls
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner : ConversationRunner} {before : Model}
    (box : TransportRoundBox cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier runner before) : Prop :=
  box.round.accepted.validated.response.choices.head.message.toolCalls.length = 0

end TransportRoundBox

inductive TransportTrace
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
      TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
        runner before runner before
  | cons
      {runner : ConversationRunner}
      {before : Model}
      {finalRunner : ConversationRunner}
      {finalModel : Model}
      (head : TransportRoundBox cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before)
      (tail : TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
        head.round.finalRunner head.round.finalModel finalRunner finalModel) :
      TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
        runner before finalRunner finalModel

namespace TransportTrace

def length
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model} :
    TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
      runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons _ tail => Nat.succ tail.length

theorem length_cons
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before : Model}
    {finalModel : Model}
    (head : TransportRoundBox cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier runner before)
    (tail : TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
      head.round.finalRunner head.round.finalModel finalRunner finalModel) :
    length (.cons head tail) = Nat.succ (length tail) :=
  rfl

end TransportTrace

/-! ## Completion and run result -/

inductive TransportStop
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
      (last : TransportRoundBox cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
        sourcesEarlier runner before)
      (runner_eq : last.round.finalRunner = finalRunner)
      (model_eq : last.round.finalModel = finalModel)
      (noToolCalls : TransportRoundBox.noToolCalls last)
  | fuelExhausted

namespace TransportStop

def isCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    TransportStop cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
      finalRunner finalModel → Bool
  | .completed .. => true
  | .fuelExhausted => false

def isFuelExhausted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    TransportStop cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
      finalRunner finalModel → Bool
  | .completed .. => false
  | .fuelExhausted => true

end TransportStop

structure TransportConversationRunResult
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
  trace : TransportTrace cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
    initialRunner initialModel finalRunner finalModel
  stop : TransportStop cfg baseUrl apiKey source sourceEventSeqs sourcesNodup sourcesEarlier
    finalRunner finalModel

/-! ## Single-decoder fuel-bounded execution -/

def runTransportAux
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
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          TransportConversationRunResult cfg baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      match ← executeSource transport baseUrl apiKey source cfg before runner sourceEventSeqs
          sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨plan, ⟨body, round⟩⟩ =>
          let head : TransportRoundBox cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
              sourcesEarlier runner before := { plan, body, round }
          if noTools :
              head.round.accepted.validated.response.choices.head.message.toolCalls.length = 0 then
            pure (.ok ⟨round.finalRunner, ⟨round.finalModel, {
              trace := .cons head (.nil round.finalRunner round.finalModel)
              stop := .completed head rfl rfl noTools
            }⟩⟩)
          else
            match ← runTransportAux fuel transport baseUrl apiKey source sourceEventSeqs
                sourcesNodup sourcesEarlier round.finalModel round.finalRunner with
            | .error error => pure (.error error)
            | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                pure (.ok ⟨finalRunner, ⟨finalModel, {
                  trace := .cons head tail.trace
                  stop := tail.stop
                }⟩⟩)

def runTransport
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
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          TransportConversationRunResult cfg baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier runner before finalRunner finalModel)) :=
  runTransportAux fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier before runner

end Cordis.DeepSeekHarnessTransportConversation
