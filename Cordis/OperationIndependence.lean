import Cordis.OperationalEquivalence
import Cordis.QuotientEffect
import Cordis.CoeffectQuotient
import Cordis.Batch
import Cordis.Schedule
import Cordis.Transformation

/-!
# Finite operation independence and mediated computations

This module mechanizes the strongest isolated finite form of CORDIS paper Definitions 39--41
and Theorem 40 at revision `948a07b369c62adb3b12e102458be5c18dfb69b9`.

`runLocal` executes Definition 34 generator words while retaining their final value and
heterogeneous outcomes. `transformAt` lifts the resulting finite transformations to one key of
the dependent context. `FiniteKeyIndependent` states monoid-word commutation together with
stability of the complete forward result: successor, state-dependent yielded inverse, and typed
outcome. The distinct-key theorem proves this stronger equality-level property for arbitrary
finite words, not merely for adjacent forward calls.

`Computation` is Definition 41's outcome-indexed free syntax. Its interpreter performs one
typed lifted operation, selects the continuation by the heterogeneous outcome, and composes
the local and continuation inverses in LIFO order.

Theorem 42 is not asserted here. Moving from pairwise operation-word laws to arbitrary
outcome-dependent trees requires a closure theorem tracking every realized branch, the
generators it exposes, and equality of differently yielded continuation inverses. The paper's
informal occurrence set does not itself provide that indexed witness, and the `PairedGap`
counterexample in `OperationalEquivalence` shows why differently yielded inverses cannot be
silently identified. `MediatedClosure` below names the exact additional computation-level law
needed before a bounded Theorem 42 statement can be made.

The module does not claim arbitrary paper transformation monoids beyond finite words,
Theorem 42 without `MediatedClosure`, external parallel execution, or component/fiber traces.
-/

set_option autoImplicit false

namespace Cordis.OperationIndependence

universe u v w

/-!
## Definition 39 for exact total operation interpretations
-/

/-- A total reversible operation together with its typed observable outcome. -/
structure ExactOperation (State : Type u) (Outcome : Type v) where
  /-- The operation's proof-carrying state transition. -/
  effect : Cordis.Effect State
  /-- The outcome observed at the state where the operation is invoked. -/
  outcome : State → Outcome

/-- One foreign transformation leaves an exact operation's outcome unchanged. -/
def OutcomeStable {State : Type u} {Outcome : Type v}
    (operation : ExactOperation State Outcome)
    (map : Transformation.Endomorphism State) : Prop :=
  ∀ state, operation.outcome (map state) = operation.outcome state

/-- Identity leaves every operation outcome unchanged. -/
theorem outcomeStable_id {State : Type u} {Outcome : Type v}
    (operation : ExactOperation State Outcome) : OutcomeStable operation id :=
  fun _ ↦ rfl

/-- Outcome stability is closed under transformation composition. -/
theorem OutcomeStable.comp
    {State : Type u} {Outcome : Type v}
    {operation : ExactOperation State Outcome}
    {outer inner : Transformation.Endomorphism State}
    (outerStable : OutcomeStable operation outer)
    (innerStable : OutcomeStable operation inner) :
    OutcomeStable operation (outer ∘ inner) := by
  intro state
  exact Eq.trans (outerStable (inner state)) (innerStable state)

/-- Stability under every generator extends to its complete transformation monoid. -/
theorem outcomeStable_of_generators
    {State : Type u} {Outcome : Type v}
    {Generator : Transformation.Endomorphism State → Prop}
    {operation : ExactOperation State Outcome}
    (generatorsStable : ∀ {map}, Generator map → OutcomeStable operation map)
    {map : Transformation.Endomorphism State}
    (member : Transformation.Closure Generator map) : OutcomeStable operation map := by
  induction member with
  | identity => exact outcomeStable_id operation
  | generator generated => exact generatorsStable generated
  | comp _ _ outerHypothesis innerHypothesis => exact outerHypothesis.comp innerHypothesis

/-- Definition 39 for total exact effects, including full monoid closure.

The `effects` field is the complete Definition 19 certificate from `Cordis.Transformation`, so
it includes commutation of all generated forward/inverse words and stability of differently
yielded inverses. The remaining fields are Equation (35) in both directions.
-/
structure ExactOperationIndependent
    {State : Type u} {FirstOutcome : Type v} {SecondOutcome : Type w}
    (first : ExactOperation State FirstOutcome)
    (second : ExactOperation State SecondOutcome) : Prop where
  /-- Full Definition 19 independence of the reversible effects. -/
  effects : Transformation.Independent first.effect second.effect
  /-- Every second-operation transformation preserves the first outcome. -/
  first_outcome_stable : ∀ {map}, Transformation.OfEffect second.effect map →
    OutcomeStable first map
  /-- Every first-operation transformation preserves the second outcome. -/
  second_outcome_stable : ∀ {map}, Transformation.OfEffect first.effect map →
    OutcomeStable second map

namespace ExactOperationIndependent

/-- Generator laws promote to the full Definition 39 certificate. -/
theorem of_generators
    {State : Type u} {FirstOutcome : Type v} {SecondOutcome : Type w}
    {first : ExactOperation State FirstOutcome}
    {second : ExactOperation State SecondOutcome}
    (commute : ∀ {left right},
      Transformation.EffectGenerator first.effect left →
      Transformation.EffectGenerator second.effect right →
      Transformation.Commutes left right)
    (firstInverseStable : ∀ {map},
      Transformation.EffectGenerator second.effect map →
      Transformation.InverseStable first.effect map)
    (secondInverseStable : ∀ {map},
      Transformation.EffectGenerator first.effect map →
      Transformation.InverseStable second.effect map)
    (firstOutcomeStable : ∀ {map},
      Transformation.EffectGenerator second.effect map → OutcomeStable first map)
    (secondOutcomeStable : ∀ {map},
      Transformation.EffectGenerator first.effect map → OutcomeStable second map) :
    ExactOperationIndependent first second where
  effects := Transformation.Independent.of_generators commute
    firstInverseStable secondInverseStable
  first_outcome_stable := outcomeStable_of_generators firstOutcomeStable
  second_outcome_stable := outcomeStable_of_generators secondOutcomeStable

/-- Full Definition 39 implies exact equality of the two adjacent proof-carrying orders. -/
theorem seq_effect_eq
    {State : Type u} {FirstOutcome : Type v} {SecondOutcome : Type w}
    {first : ExactOperation State FirstOutcome}
    {second : ExactOperation State SecondOutcome}
    (independent : ExactOperationIndependent first second) :
    Cordis.Effect.seq first.effect second.effect =
      Cordis.Effect.seq second.effect first.effect :=
  independent.effects.seq_commute

end ExactOperationIndependent

/-!
## Finite local transformation words
-/

variable {State : Type u}

/-- A successful local word retains its final state and all heterogeneous forward outcomes. -/
structure LocalRun (coeffect : Coeffect.CoeffectAt State) where
  /-- Value left by the finite transformation word. -/
  after : State
  /-- Forward outcomes, in execution order. -/
  outcomes : List (OperationalEquivalence.OutcomeEvent coeffect)

/-- Execute a finite word of forward and concrete yielded-inverse generators. -/
def runLocal (coeffect : Coeffect.CoeffectAt State) :
    OperationalEquivalence.Test coeffect → State → Option (LocalRun coeffect)
  | [], state => some ⟨state, []⟩
  | letter :: rest, state =>
      match letter with
      | .forward op input =>
          letI := coeffect.enabledDecidable op input state
          if enabled : coeffect.Enabled op input state then
            let result := coeffect.run op input state enabled
            match runLocal coeffect rest result.1.after with
            | none => none
            | some suffix => some ⟨suffix.after, ⟨op, result.2⟩ :: suffix.outcomes⟩
          else
            none
      | .inverse op input seed enabled =>
          runLocal coeffect rest ((coeffect.run op input seed enabled).1.undo state)

/-- Forget outcomes and retain only a finite word's state transformation. -/
def localTransition (coeffect : Coeffect.CoeffectAt State)
    (word : OperationalEquivalence.Test coeffect) (state : State) : Option State :=
  (runLocal coeffect word state).map LocalRun.after

@[simp]
theorem runLocal_nil (coeffect : Coeffect.CoeffectAt State) (state : State) :
    runLocal coeffect [] state = some ⟨state, []⟩ := rfl

/-!
## Generic one-key transformations
-/

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- Lift a possibly undefined local value transformation to one dependent context key. -/
def applyLocal (context : Coeffect.Context Key Value) (key : Key)
    (transition : Value key → Option (Value key)) : Option (Coeffect.Context Key Value) :=
  match context key with
  | none => none
  | some value =>
      match transition value with
      | none => none
      | some after => some (Coeffect.setAt context key after)

/-- A successful one-key transformation leaves every distinct binding exactly unchanged. -/
theorem applyLocal_lookup_other
    (context after : Coeffect.Context Key Value) (target key : Key)
    (transition : Value target → Option (Value target)) (different : key ≠ target)
    (ran : applyLocal context target transition = some after) : after key = context key := by
  unfold applyLocal at ran
  cases lookup : context target with
  | none => simp [lookup] at ran
  | some value =>
      cases changed : transition value with
      | none => simp [lookup, changed] at ran
      | some next =>
          simp [lookup, changed] at ran
          subst after
          exact Coeffect.setAt_other context target key next different

/-- Arbitrary local transformations at distinct keys commute, including undefinedness. -/
theorem applyLocal_commute
    (context : Coeffect.Context Key Value) (left right : Key) (different : left ≠ right)
    (leftTransition : Value left → Option (Value left))
    (rightTransition : Value right → Option (Value right)) :
    (applyLocal context left leftTransition).bind
        (fun after ↦ applyLocal after right rightTransition) =
      (applyLocal context right rightTransition).bind
        (fun after ↦ applyLocal after left leftTransition) := by
  cases leftLookup : context left with
  | none =>
      cases rightLookup : context right with
      | none => simp [applyLocal, leftLookup, rightLookup]
      | some rightValue =>
          cases rightResult : rightTransition rightValue with
          | none => simp [applyLocal, leftLookup, rightLookup, rightResult]
          | some rightAfter =>
              simp [applyLocal, leftLookup, rightLookup, rightResult, different]
  | some leftValue =>
      cases rightLookup : context right with
      | none =>
          cases leftResult : leftTransition leftValue with
          | none => simp [applyLocal, leftLookup, rightLookup, leftResult]
          | some leftAfter =>
              simp [applyLocal, leftLookup, rightLookup, leftResult, Ne.symm different]
      | some rightValue =>
          cases leftResult : leftTransition leftValue with
          | none =>
              cases rightResult : rightTransition rightValue with
              | none => simp [applyLocal, leftLookup, rightLookup, leftResult, rightResult]
              | some rightAfter =>
                  simp [applyLocal, leftLookup, rightLookup, leftResult, rightResult, different]
          | some leftAfter =>
              cases rightResult : rightTransition rightValue with
              | none =>
                  simp [applyLocal, leftLookup, rightLookup, leftResult, rightResult,
                    Ne.symm different]
              | some rightAfter =>
                  simp [applyLocal, leftLookup, rightLookup, leftResult, rightResult,
                    different, Ne.symm different, Coeffect.setAt_commute]

/-!
## Lifted operation words and Definition 39 data
-/

/-- Lift one finite local generator word to its dependent context key. -/
def transformAt (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)) (key : Key)
    (word : OperationalEquivalence.Test (coeffects key))
    (context : Coeffect.Context Key Value) : Option (Coeffect.Context Key Value) :=
  applyLocal context key (localTransition (coeffects key) word)

/-- Data yielded by one enabled forward operation, before lifting to the whole context. -/
structure ForwardData (coeffect : Coeffect.CoeffectAt State) (op : coeffect.Op) where
  /-- Local successor. -/
  after : State
  /-- State-dependent yielded inverse. -/
  undo : State → State
  /-- Heterogeneous typed outcome. -/
  outcome : coeffect.Outcome op

/-- Inspect the full local result yielded by a forward operation at one context key. -/
def inspectForwardAt
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)) (key : Key)
    (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (context : Coeffect.Context Key Value) : Option (ForwardData (coeffects key) op) :=
  match context key with
  | none => none
  | some value =>
      letI := (coeffects key).enabledDecidable op input value
      if enabled : (coeffects key).Enabled op input value then
        let result := (coeffects key).run op input value enabled
        some ⟨result.1.after, result.1.undo, result.2⟩
      else
        none

/-- A successful transformation at another key preserves successor, inverse, and outcome data. -/
theorem inspectForwardAt_stable_of_other
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (target other : Key) (different : target ≠ other)
    (op : (coeffects target).Op) (input : (coeffects target).Input op)
    (context after : Coeffect.Context Key Value)
    (transition : Value other → Option (Value other))
    (ran : applyLocal context other transition = some after) :
    inspectForwardAt coeffects target op input after =
      inspectForwardAt coeffects target op input context := by
  have lookup := applyLocal_lookup_other context after other target transition different ran
  simp only [inspectForwardAt]
  rw [lookup]

/-- Finite Definition 39 independence for all operation generators at two keys.

`words_commute` is the finite transformation-monoid clause. The stability fields retain the
entire forward result, including the yielded inverse and typed outcome, under every successful
foreign word.
-/
structure FiniteKeyIndependent
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (left right : Key) : Prop where
  /-- Every finite generator word at one key commutes with every word at the other. -/
  words_commute :
    ∀ (leftWord : OperationalEquivalence.Test (coeffects left))
      (rightWord : OperationalEquivalence.Test (coeffects right)) context,
      (transformAt coeffects left leftWord context).bind
          (transformAt coeffects right rightWord) =
        (transformAt coeffects right rightWord context).bind
          (transformAt coeffects left leftWord)
  /-- Foreign right-key words do not disturb left operation results or yielded inverses. -/
  left_data_stable :
    ∀ (op : (coeffects left).Op) (input : (coeffects left).Input op)
      (rightWord : OperationalEquivalence.Test (coeffects right)) context after,
      transformAt coeffects right rightWord context = some after →
      inspectForwardAt coeffects left op input after =
        inspectForwardAt coeffects left op input context
  /-- Foreign left-key words do not disturb right operation results or yielded inverses. -/
  right_data_stable :
    ∀ (op : (coeffects right).Op) (input : (coeffects right).Input op)
      (leftWord : OperationalEquivalence.Test (coeffects left)) context after,
      transformAt coeffects left leftWord context = some after →
      inspectForwardAt coeffects right op input after =
        inspectForwardAt coeffects right op input context

/-- Theorem 40 for the modeled finite generator-word language. -/
theorem distinctKeys_finiteIndependent
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (left right : Key) (different : left ≠ right) :
    FiniteKeyIndependent coeffects left right where
  words_commute := by
    intro leftWord rightWord context
    exact applyLocal_commute context left right different
      (localTransition (coeffects left) leftWord)
      (localTransition (coeffects right) rightWord)
  left_data_stable := by
    intro op input rightWord context after ran
    exact inspectForwardAt_stable_of_other coeffects left right different op input
      context after (localTransition (coeffects right) rightWord) ran
  right_data_stable := by
    intro op input leftWord context after ran
    exact inspectForwardAt_stable_of_other coeffects right left (Ne.symm different) op input
      context after (localTransition (coeffects left) leftWord) ran

/-!
## Definition 41: outcome-mediated computations
-/

/-- Definition 41's least outcome-indexed computation syntax. -/
inductive Computation
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)) where
  /-- The unit computation. -/
  | pure
  /-- Perform one operation and choose the continuation from its typed outcome. -/
  | step (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
      (next : (coeffects key).Outcome op → Computation coeffects)

namespace Computation

/-- Interpret a mediated computation as a possibly undefined witnessed context effect. -/
def run (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)) :
    Computation coeffects →
      (context : Coeffect.Context Key Value) →
        Option (Cordis.Applied (Coeffect.Context Key Value) context)
  | .pure, context => some (Cordis.Effect.identity context)
  | .step key op input next, context =>
      match lookup : context key with
      | none => none
      | some value =>
          let present : Coeffect.Present context key := ⟨value, lookup⟩
          letI := (coeffects key).enabledDecidable op input value
          if enabled : (coeffects key).Enabled op input value then
            let stage := (coeffects key).lift op input context present enabled
            match run coeffects (next stage.2) stage.1.after with
            | none => none
            | some continuation =>
                some {
                  after := continuation.after
                  undo := stage.1.undo ∘ continuation.undo
                  undo_after := by
                    exact Eq.trans (congrArg stage.1.undo continuation.undo_after)
                      stage.1.undo_after
                }
          else
            none

@[simp]
theorem run_pure
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (context : Coeffect.Context Key Value) :
    run coeffects .pure context = some (Cordis.Effect.identity context) := rfl

/-- Every successful mediated computation carries exact LIFO recovery by construction. -/
theorem run_recovers
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (computation : Computation coeffects) (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before)
    (_ran : computation.run coeffects before = some applied) :
    applied.undo applied.after = before := by
  exact applied.undo_after

end Computation

/-!
## Exact examples and a forward-only counterexample
-/

namespace Example

namespace Exact

open Cordis.Transformation.Example

/-- The left operation returns a number while changing only the left coordinate. -/
def leftOperation : ExactOperation Model Nat where
  effect := bumpLeft
  outcome := fun state ↦ state.left

/-- The right operation returns a Boolean while changing only the right coordinate. -/
def rightOperation : ExactOperation Model Bool where
  effect := bumpRight
  outcome := fun state ↦ state.right % 2 == 0

theorem leftOutcome_generators_stable :
    ∀ {map : Transformation.Endomorphism Model},
      Transformation.EffectGenerator bumpRight map → OutcomeStable leftOperation map := by
  intro map generated state
  cases generated <;> rfl

theorem rightOutcome_generators_stable :
    ∀ {map : Transformation.Endomorphism Model},
      Transformation.EffectGenerator bumpLeft map → OutcomeStable rightOperation map := by
  intro map generated state
  cases generated <;> rfl

/-- Full Definition 39, not merely adjacent successor commutation. -/
theorem independent : ExactOperationIndependent leftOperation rightOperation where
  effects := Cordis.Transformation.Example.independent
  first_outcome_stable := outcomeStable_of_generators leftOutcome_generators_stable
  second_outcome_stable := outcomeStable_of_generators rightOutcome_generators_stable

example :
    Cordis.Effect.seq leftOperation.effect rightOperation.effect =
      Cordis.Effect.seq rightOperation.effect leftOperation.effect :=
  independent.seq_effect_eq

end Exact

namespace DistinctKeys

open Cordis.Coeffect.Quotient.Example

def counterSeed : ExampleValue .counter := show Nat from 3
theorem counterEnabled : counterCoeffect.Enabled counterOp counterAmount counterSeed := trivial

def counterWord : OperationalEquivalence.Test counterCoeffect :=
  [.forward counterOp counterAmount,
    .inverse counterOp counterAmount counterSeed counterEnabled]

def labelOp : labelCoeffect.Op := show Unit from ()
def labelInput : labelCoeffect.Input labelOp := show String from "-next"
def labelWord : OperationalEquivalence.Test labelCoeffect :=
  [.forward labelOp labelInput]

theorem independent : FiniteKeyIndependent coeffects .counter .label :=
  distinctKeys_finiteIndependent coeffects .counter .label (by
    intro equal
    cases equal)

/-- The two whole finite words commute as lifted, possibly undefined transformations. -/
example :
    (transformAt coeffects .counter counterWord left).bind
        (transformAt coeffects .label labelWord) =
      (transformAt coeffects .label labelWord left).bind
        (transformAt coeffects .counter counterWord) :=
  independent.words_commute counterWord labelWord left

/-- The label word preserves the counter operation's successor, inverse, and `Nat` outcome. -/
example (after : Coeffect.Context ExampleKey ExampleValue)
    (ran : transformAt coeffects .label labelWord left = some after) :
    inspectForwardAt coeffects .counter counterOp counterAmount after =
      inspectForwardAt coeffects .counter counterOp counterAmount left :=
  independent.left_data_stable counterOp counterAmount labelWord left after ran

end DistinctKeys

namespace Mediated

open Cordis.Coeffect.Quotient.Example

/-- The counter's `Nat` outcome chooses the string argument of the next operation. -/
def computation : Computation coeffects :=
  .step .counter counterOp counterAmount (fun previous ↦
    .step .label DistinctKeys.labelOp
      (if (show Nat from previous) = 3 then
        show String from "-three"
      else
        show String from "-other")
      (fun _ ↦ .pure))

theorem run_isSome : (computation.run coeffects left).isSome = true := rfl

def applied : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue) left :=
  (computation.run coeffects left).get run_isSome

def expectedCounter : ExampleValue .counter := show Nat from 7
def expectedLabel : ExampleValue .label := show String from "a-three"

example : applied.after .counter = some expectedCounter := rfl
example : applied.after .label = some expectedLabel := rfl
example : applied.undo applied.after = left := applied.undo_after

end Mediated

namespace ForwardOnlyGap

/-- Two coordinates whose forward updates commute. -/
structure Model where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

/-- The forward map changes only `x`, but its off-successor inverse behavior captures `y`. -/
def sensitiveX : Cordis.Effect Model := fun before ↦
  let successor := { before with x := before.x + 1 }
  {
    after := successor
    undo := fun current ↦
      if current = successor then before else { current with x := before.y }
    undo_after := by simp
  }

def bumpY : Cordis.Effect Model := fun before ↦
  {
    after := { before with y := before.y + 1 }
    undo := fun current ↦ { current with y := current.y - 1 }
    undo_after := by cases before; simp
  }

theorem forward_maps_commute :
    Transformation.Commutes
      (fun state ↦ (sensitiveX state).after)
      (fun state ↦ (bumpY state).after) := by
  intro state
  cases state
  rfl

def seed : Model := { x := 0, y := 5 }
def probe : Model := { x := 100, y := 100 }

/-- Foreign forward motion changes the inverse yielded by `sensitiveX`. -/
theorem inverse_stability_fails :
    ¬Transformation.InverseStable sensitiveX (fun state ↦ (bumpY state).after) := by
  intro stable
  have functionsEqual := stable seed
  have valuesEqual := congrArg (fun undo ↦ undo probe) functionsEqual
  simp [sensitiveX, bumpY, seed, probe] at valuesEqual

end ForwardOnlyGap

end Example

/-!
## The named closure boundary for Theorem 42
-/

/-- The additional computation-level closure needed to state a bounded Theorem 42 honestly.

This law is stronger than adjacent call commutation. It quantifies over complete mediated trees,
their outcome-selected branches, and the different composite inverses those branches yield.
-/
structure MediatedClosure
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key))
    (left right : Computation coeffects) : Prop where
  /-- Both execution orders agree on definedness and complete proof-carrying results. -/
  orders_agree : ∀ before,
    match left.run coeffects before, right.run coeffects before with
    | none, none => True
    | some leftApplied, some rightApplied =>
        match right.run coeffects leftApplied.after,
          left.run coeffects rightApplied.after with
        | some leftThenRight, some rightThenLeft =>
            leftThenRight.after = rightThenLeft.after ∧
            (∀ current,
              leftApplied.undo (leftThenRight.undo current) =
                rightApplied.undo (rightThenLeft.undo current))
        | _, _ => False
    | _, _ => False
  /-- Every foreign mediated transformation preserves the complete yielded inverse. -/
  yielded_inverse_stable : ∀ before leftApplied rightApplied,
    left.run coeffects before = some leftApplied →
    right.run coeffects before = some rightApplied →
    (∀ current,
      leftApplied.undo current =
        (match left.run coeffects rightApplied.after with
        | some moved => moved.undo current
        | none => leftApplied.undo current)) ∧
    (∀ current,
      rightApplied.undo current =
        (match right.run coeffects leftApplied.after with
        | some moved => moved.undo current
        | none => rightApplied.undo current))

/-!
`MediatedClosure` is intentionally not derived from a pairwise key predicate in this bounded
module. Doing so is the missing branch-indexed transformation-monoid closure proof corresponding
to the paper's Theorem 42. Naming it prevents a finite adjacent-swap certificate from being
misreported as that theorem.
-/

end Cordis.OperationIndependence
