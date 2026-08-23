import Cordis.DeepSeekSchemaConversation

/-!
# Intrinsic history for heterogeneous schema rounds

`DeepSeekSchemaConversationLoop` already retains a convenient list of successful tool rounds.
This module supplies the stronger API boundary that list alone cannot express: each round is
indexed by the runner/model at which it starts, and the next trace node is indexed by the exact
runner/model produced by that round.  The trace stops before a terminal no-tool response or at
fuel exhaustion; the stop witness remains in the loop result.

This is a pure history certificate.  It does not add transport, retry, cancellation, persistence,
provider obedience, external effects, or deployed Harness semantics.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaTrace

open Cordis
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaConversation

universe u

abbrev RoundWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) :=
  Sigma fun runner : ConversationRunner =>
    Sigma fun before : Model =>
      Sigma fun body : String =>
        Sigma fun accepted : AcceptedToolCalls body =>
          Sigma fun batch : RegistryExecutionBatch cfg before accepted.calls =>
            SchemaRegistryConversationResult registry runner before accepted batch

inductive SchemaConversationTrace
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) :
    ConversationRunner -> Model -> ConversationRunner -> Model -> Type where
  | nil (runner : ConversationRunner) (before : Model) :
      SchemaConversationTrace registry runner before runner before
  | snoc
      {initialRunner : ConversationRunner}
      {initialModel : Model}
      {runner : ConversationRunner}
      {before : Model}
      {body : String}
      {accepted : AcceptedToolCalls body}
      {batch : RegistryExecutionBatch cfg before accepted.calls}
      (prior : SchemaConversationTrace registry initialRunner initialModel runner before)
      (round : SchemaRegistryConversationResult registry runner before accepted batch) :
      SchemaConversationTrace registry initialRunner initialModel
        round.round.finalRunner round.batch.finalModel

namespace SchemaConversationTrace

def rounds
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {initialRunner : ConversationRunner} {initialModel : Model}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    SchemaConversationTrace registry initialRunner initialModel finalRunner finalModel ->
      List (RoundWitness registry)
  | .nil _ _ => []
  | .snoc prior round =>
      prior.rounds ++ [⟨_, ⟨_, ⟨_, ⟨_, ⟨_, round⟩⟩⟩⟩⟩]

def length
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {initialRunner : ConversationRunner} {initialModel : Model}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    SchemaConversationTrace registry initialRunner initialModel finalRunner finalModel -> Nat
  | .nil _ _ => 0
  | .snoc prior _ => prior.length + 1

@[simp] theorem rounds_nil
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner} {before : Model} :
    (SchemaConversationTrace.nil runner before :
      SchemaConversationTrace registry runner before runner before).rounds = [] :=
  rfl

@[simp] theorem length_nil
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner} {before : Model} :
    (SchemaConversationTrace.nil runner before :
      SchemaConversationTrace registry runner before runner before).length = 0 :=
  rfl

@[simp] theorem rounds_length
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {initialRunner : ConversationRunner} {initialModel : Model}
    {finalRunner : ConversationRunner} {finalModel : Model}
    (trace : SchemaConversationTrace registry initialRunner initialModel finalRunner finalModel) :
    trace.rounds.length = trace.length := by
  induction trace with
  | nil => rfl
  | snoc prior round ih => simp [SchemaConversationTrace.rounds,
      SchemaConversationTrace.length, ih]

@[simp] theorem last_round_is_endpoint
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {initialRunner : ConversationRunner} {initialModel : Model}
    {runner : ConversationRunner} {before : Model}
    {body : String} {accepted : AcceptedToolCalls body}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (prior : SchemaConversationTrace registry initialRunner initialModel runner before)
    (round : SchemaRegistryConversationResult registry runner before accepted batch) :
    (SchemaConversationTrace.snoc prior round).rounds.getLast? =
      some ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, round⟩⟩⟩⟩⟩ := by
  simp [SchemaConversationTrace.rounds]

theorem round_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner} {before : Model}
    {body : String} {accepted : AcceptedToolCalls body}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (round : SchemaRegistryConversationResult registry runner before accepted batch) :
    round.round.finalRunner.session.nextSeq =
      round.round.assistantRunner.session.nextSeq + round.batch.executions.length :=
  round.finalRunner_nextSeq

end SchemaConversationTrace

end Cordis.DeepSeekSchemaTrace
