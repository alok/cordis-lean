import Cordis.GlobalActivationOrchestrationTransposition
import Cordis.GlobalTraceFacts

/-!
# Exact adjacent rewriting of intrinsic global traces

This module turns the repository's corrected two-step activation transposition theorems into actual
rewrites of dependent `GlobalCalculus.Trace` values. Every rewrite preserves the exact outer source
and endpoint in its type; rule and actor equations certify that the replacement is the intended
adjacent transposition rather than an unrelated path between the same states.

Fixed-program occurrence evidence is explicit. Bare lifecycle transitions do not determine a
program, root, reachable code, or registration oracle, so trace assignments are supplied and are
reconstructed after every assigned rewrite.

This is an exact-state local rewrite layer, not paper Lemma 72 or Theorem 73. It deliberately
excludes registering activation followed by O-Insert, birth-erased or renamed endpoints, arbitrary
permutation normalization, vestigial deletion, canonical forms, confluence, and termination.
-/

set_option autoImplicit false

namespace Cordis.GlobalTraceRewrite

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts
open Cordis.GlobalIteratorIndependence Cordis.GlobalActivationTransposition
open Cordis.GlobalActivationOrchestrationTransposition
open Cordis.GlobalLandingTransposition

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Exact two-step paths and swap certificates -/

structure StepPair
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics)
    (before after : State catalog Ambient) where
  middle : State catalog Ambient
  first : Step dynamics inertia before middle
  second : Step dynamics inertia middle after

namespace StepPair

def trace
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) :
    Cordis.GlobalCalculus.Trace dynamics inertia before after :=
  .cons pair.first (.cons pair.second (.nil after))

def rules
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : List Cordis.GlobalCalculus.Rule :=
  [pair.first.rule, pair.second.rule]

def actors
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : List (Actor sig.Name) :=
  [pair.first.actor, pair.second.actor]

def firstRecord
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : StepRecord dynamics inertia :=
  ⟨before, pair.middle, pair.first⟩

def secondRecord
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : StepRecord dynamics inertia :=
  ⟨pair.middle, after, pair.second⟩

@[simp] theorem trace_rules
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : pair.trace.rules = pair.rules := rfl

@[simp] theorem trace_actors
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) : pair.trace.actors = pair.actors := rfl

@[simp] theorem trace_records
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (pair : StepPair dynamics inertia before after) :
    Cordis.GlobalTraceFacts.Trace.records pair.trace =
      [pair.firstRecord, pair.secondRecord] := rfl

end StepPair

structure ExactAdjacentSwap
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (normal : StepPair dynamics inertia before after) where
  swapped : StepPair dynamics inertia before after
  first_rule : swapped.first.rule = normal.second.rule
  second_rule : swapped.second.rule = normal.first.rule
  first_actor : swapped.first.actor = normal.second.actor
  second_actor : swapped.second.actor = normal.first.actor

/-! ## Trace projections and exact located windows -/

namespace Trace

theorem rules_append
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : Cordis.GlobalCalculus.Trace dynamics inertia start middle)
    (right : Cordis.GlobalCalculus.Trace dynamics inertia middle finish) :
    (Cordis.GlobalTraceFacts.Trace.append left right).rules = left.rules ++ right.rules := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp [Cordis.GlobalTraceFacts.Trace.append, Cordis.GlobalCalculus.Trace.rules, ih]

theorem actors_append
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : Cordis.GlobalCalculus.Trace dynamics inertia start middle)
    (right : Cordis.GlobalCalculus.Trace dynamics inertia middle finish) :
    (Cordis.GlobalTraceFacts.Trace.append left right).actors = left.actors ++ right.actors := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp [Cordis.GlobalTraceFacts.Trace.append, Cordis.GlobalCalculus.Trace.actors, ih]

theorem records_append
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : Cordis.GlobalCalculus.Trace dynamics inertia start middle)
    (right : Cordis.GlobalCalculus.Trace dynamics inertia middle finish) :
    Cordis.GlobalTraceFacts.Trace.records
        (Cordis.GlobalTraceFacts.Trace.append left right) =
      Cordis.GlobalTraceFacts.Trace.records left ++
        Cordis.GlobalTraceFacts.Trace.records right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp [Cordis.GlobalTraceFacts.Trace.append, Cordis.GlobalTraceFacts.Trace.records, ih]

end Trace

structure AdjacentOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final) where
  windowStart : State catalog Ambient
  windowEnd : State catalog Ambient
  beforeTrace : Cordis.GlobalCalculus.Trace dynamics inertia initial windowStart
  pair : StepPair dynamics inertia windowStart windowEnd
  afterTrace : Cordis.GlobalCalculus.Trace dynamics inertia windowEnd final
  decomposition : trace = Cordis.GlobalTraceFacts.Trace.append beforeTrace
    (.cons pair.first (.cons pair.second afterTrace))

namespace AdjacentOccurrence

def rewrite
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    Cordis.GlobalCalculus.Trace dynamics inertia initial final :=
  Cordis.GlobalTraceFacts.Trace.append occurrence.beforeTrace
    (.cons swap.swapped.first (.cons swap.swapped.second occurrence.afterTrace))

theorem first_mem_records
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace) :
    occurrence.pair.firstRecord ∈ Cordis.GlobalTraceFacts.Trace.records trace := by
  have recordsEq := congrArg Cordis.GlobalTraceFacts.Trace.records occurrence.decomposition
  rw [recordsEq, Trace.records_append]
  simp [Cordis.GlobalTraceFacts.Trace.records, StepPair.firstRecord]

theorem second_mem_records
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace) :
    occurrence.pair.secondRecord ∈ Cordis.GlobalTraceFacts.Trace.records trace := by
  have recordsEq := congrArg Cordis.GlobalTraceFacts.Trace.records occurrence.decomposition
  rw [recordsEq, Trace.records_append]
  simp [Cordis.GlobalTraceFacts.Trace.records, StepPair.secondRecord]

theorem original_rules
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace) :
    trace.rules = occurrence.beforeTrace.rules ++ occurrence.pair.first.rule ::
      occurrence.pair.second.rule :: occurrence.afterTrace.rules := by
  have rulesEq := congrArg Cordis.GlobalCalculus.Trace.rules occurrence.decomposition
  calc
    trace.rules =
        (Cordis.GlobalTraceFacts.Trace.append occurrence.beforeTrace
          (.cons occurrence.pair.first
            (.cons occurrence.pair.second occurrence.afterTrace))).rules := rulesEq
    _ = _ := by rw [Trace.rules_append]; rfl

theorem rewrite_rules
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).rules =
      occurrence.beforeTrace.rules ++ occurrence.pair.second.rule ::
        occurrence.pair.first.rule :: occurrence.afterTrace.rules := by
  rw [rewrite, Trace.rules_append]
  simp [Cordis.GlobalCalculus.Trace.rules, swap.first_rule, swap.second_rule]

theorem original_actors
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace) :
    trace.actors = occurrence.beforeTrace.actors ++ occurrence.pair.first.actor ::
      occurrence.pair.second.actor :: occurrence.afterTrace.actors := by
  have actorsEq := congrArg Cordis.GlobalCalculus.Trace.actors occurrence.decomposition
  calc
    trace.actors =
        (Cordis.GlobalTraceFacts.Trace.append occurrence.beforeTrace
          (.cons occurrence.pair.first
            (.cons occurrence.pair.second occurrence.afterTrace))).actors := actorsEq
    _ = _ := by rw [Trace.actors_append]; rfl

theorem rewrite_actors
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).actors =
      occurrence.beforeTrace.actors ++ occurrence.pair.second.actor ::
        occurrence.pair.first.actor :: occurrence.afterTrace.actors := by
  rw [rewrite, Trace.actors_append]
  simp [Cordis.GlobalCalculus.Trace.actors, swap.first_actor, swap.second_actor]

theorem rules_perm
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).rules.Perm trace.rules := by
  rw [occurrence.rewrite_rules swap, occurrence.original_rules]
  exact List.Perm.append_left occurrence.beforeTrace.rules
    (List.Perm.swap occurrence.pair.first.rule occurrence.pair.second.rule
      occurrence.afterTrace.rules)

theorem actors_perm
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).actors.Perm trace.actors := by
  rw [occurrence.rewrite_actors swap, occurrence.original_actors]
  exact List.Perm.append_left occurrence.beforeTrace.actors
    (List.Perm.swap occurrence.pair.first.actor occurrence.pair.second.actor
      occurrence.afterTrace.actors)

theorem rules_length_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).rules.length = trace.rules.length :=
  (occurrence.rules_perm swap).length_eq

theorem actors_length_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (occurrence.rewrite swap).actors.length = trace.actors.length :=
  (occurrence.actors_perm swap).length_eq

theorem rewrite_aligned
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    Cordis.GlobalTraceFacts.Trace.Aligned dynamics inertia
      (Cordis.GlobalTraceFacts.Trace.states (occurrence.rewrite swap))
      (Cordis.GlobalTraceFacts.Trace.records (occurrence.rewrite swap)) :=
  Cordis.GlobalTraceFacts.Trace.aligned _

theorem rewrite_states_length
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    (Cordis.GlobalTraceFacts.Trace.states (occurrence.rewrite swap)).length =
      (Cordis.GlobalTraceFacts.Trace.records (occurrence.rewrite swap)).length + 1 :=
  Cordis.GlobalTraceFacts.Trace.states_length _

theorem rewrite_preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair)
    (wf : WellFormed initial) : WellFormed final :=
  (occurrence.rewrite swap).preservesWellFormed wf

end AdjacentOccurrence

/-! ## Fixed-program and orchestration occurrence evidence -/

namespace ProgramActivation

def liftRule : Cordis.GlobalLifecycle.Rule → Cordis.GlobalCalculus.Rule
  | .begin => .lBegin
  | .iter => .lIter
  | .finish => .lFinish
  | .divertAbort | .divertLand => .lDivert
  | .raise => .lRaise
  | .leave => .lLeave
  | .unload => .lUnload

def globalStep
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before) :
    Step dynamics inertia before activation.after :=
  .lifecycle (activation.transition inertia)

@[simp] theorem globalStep_actor
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before) :
    (globalStep (inertia := inertia) activation).actor = .fiber program.owner := by
  cases activation with
  | begin => rfl
  | landing aligned =>
      cases aligned with
      | mk fiber present code undos committed phase target landing witness outcome =>
          cases outcome <;> rfl

@[simp] theorem globalStep_rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before) :
    (globalStep (inertia := inertia) activation).rule = liftRule activation.rule := by
  cases activation with
  | begin => rfl
  | landing aligned =>
      cases aligned with
      | mk fiber present code undos committed phase target landing witness outcome =>
          cases outcome <;> rfl

theorem globalStep_rule_eq_of_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics}
    {leftBefore rightBefore : State catalog Ambient}
    {left : Cordis.GlobalActivationTransposition.ProgramActivation leftProgram leftBefore}
    {right : Cordis.GlobalActivationTransposition.ProgramActivation rightProgram rightBefore}
    (same : left.rule = right.rule) :
    (globalStep (inertia := inertia) left).rule =
      (globalStep (inertia := inertia) right).rule := by
  rw [globalStep_rule, globalStep_rule, same]

end ProgramActivation

def transportStepAfter
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before leftAfter rightAfter : State catalog Ambient}
    (equal : leftAfter = rightAfter)
    (step : Step dynamics inertia before leftAfter) :
    Step dynamics inertia before rightAfter := by
  subst rightAfter
  exact step

@[simp] theorem transportStepAfter_rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before leftAfter rightAfter : State catalog Ambient}
    (equal : leftAfter = rightAfter)
    (step : Step dynamics inertia before leftAfter) :
    (transportStepAfter equal step).rule = step.rule := by
  cases equal
  rfl

@[simp] theorem transportStepAfter_actor
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before leftAfter rightAfter : State catalog Ambient}
    (equal : leftAfter = rightAfter)
    (step : Step dynamics inertia before leftAfter) :
    (transportStepAfter equal step).actor = step.actor := by
  cases equal
  rfl

structure ProgramOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  program : Program dynamics
  activation : Cordis.GlobalActivationTransposition.ProgramActivation program before
  after_eq : activation.after = after
  step_eq : step = after_eq ▸ ProgramActivation.globalStep (inertia := inertia) activation

namespace ProgramOccurrence

def ofActivation
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before) :
    ProgramOccurrence (ProgramActivation.globalStep (inertia := inertia) activation) where
  program := program
  activation := activation
  after_eq := rfl
  step_eq := rfl

theorem rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} {step : Step dynamics inertia before after}
    (occurrence : ProgramOccurrence step) :
    step.rule =
      (ProgramActivation.globalStep (inertia := inertia) occurrence.activation).rule := by
  obtain ⟨program, activation, afterEq, stepEq⟩ := occurrence
  cases afterEq
  exact congrArg Step.rule stepEq

theorem actor_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} {step : Step dynamics inertia before after}
    (occurrence : ProgramOccurrence step) : step.actedName = occurrence.program.owner := by
  obtain ⟨program, activation, afterEq, stepEq⟩ := occurrence
  cases afterEq
  have stepActor := congrArg Step.actedName stepEq
  calc
    step.actedName =
        (ProgramActivation.globalStep (inertia := inertia) activation).actedName := stepActor
    _ = program.owner :=
      Actor.fiber.inj (ProgramActivation.globalStep_actor (inertia := inertia) activation)

end ProgramOccurrence

structure OrchestrationOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  orchestration : OrchestrationStep before after
  step_eq : step = .orchestration orchestration

def OrchestrationOccurrence.ofOrchestration
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (orchestration : OrchestrationStep before after) :
    OrchestrationOccurrence (Step.orchestration (dynamics := dynamics)
      (inertia := inertia) orchestration) :=
  ⟨orchestration, rfl⟩

/-! ## Intrinsic trace-wide occurrence assignments -/

def IsProgramActivationRule : Cordis.GlobalCalculus.Rule → Prop
  | .lBegin | .lIter | .lFinish => True
  | _ => False

structure StepProgramAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  occurrence : IsProgramActivationRule step.rule → ProgramOccurrence step

namespace StepProgramAssignment

def ofActivation
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before) :
    StepProgramAssignment (ProgramActivation.globalStep (inertia := inertia) activation) where
  occurrence _ := ProgramOccurrence.ofActivation activation

def ofTransportedActivation
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {program : Program dynamics} {before after : State catalog Ambient}
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program before)
    (afterEq : activation.after = after) :
    StepProgramAssignment
      (transportStepAfter afterEq
        (ProgramActivation.globalStep (inertia := inertia) activation)) where
  occurrence _ := {
    program := program
    activation := activation
    after_eq := afterEq
    step_eq := by cases afterEq; rfl
  }

def ofNotActivation
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : Step dynamics inertia before after)
    (notActivation : ¬IsProgramActivationRule step.rule) : StepProgramAssignment step where
  occurrence activationRule := False.elim (notActivation activationRule)

def ofOrchestration
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    StepProgramAssignment (Step.orchestration (dynamics := dynamics)
      (inertia := inertia) step) := by
  apply ofNotActivation
  intro activationRule
  cases step <;> change False at activationRule <;> exact activationRule

def ofNonactivationLifecycle
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Transition dynamics inertia before after)
    (notActivation : ¬IsProgramActivationRule (Step.lifecycle step).rule) :
    StepProgramAssignment (Step.lifecycle step) :=
  ofNotActivation _ notActivation

end StepProgramAssignment

inductive TraceProgramAssignment
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) :
    {before after : State catalog Ambient} →
      Cordis.GlobalCalculus.Trace dynamics inertia before after → Type (u + 1) where
  | nil (state : State catalog Ambient) :
      TraceProgramAssignment dynamics inertia (.nil state)
  | cons
      {before middle after : State catalog Ambient}
      {head : Step dynamics inertia before middle}
      {tail : Cordis.GlobalCalculus.Trace dynamics inertia middle after}
      (headAssignment : StepProgramAssignment head)
      (tailAssignment : TraceProgramAssignment dynamics inertia tail) :
      TraceProgramAssignment dynamics inertia (.cons head tail)

def TraceProgramAssignment.headOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before middle after : State catalog Ambient}
    {head : Step dynamics inertia before middle}
    {tail : Cordis.GlobalCalculus.Trace dynamics inertia middle after}
    (assignment : TraceProgramAssignment dynamics inertia (.cons head tail))
    (activationRule : IsProgramActivationRule head.rule) : ProgramOccurrence head := by
  cases assignment with
  | cons headAssignment tailAssignment => exact headAssignment.occurrence activationRule

def TraceProgramAssignment.tail
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before middle after : State catalog Ambient}
    {head : Step dynamics inertia before middle}
    {tail : Cordis.GlobalCalculus.Trace dynamics inertia middle after}
    (assignment : TraceProgramAssignment dynamics inertia (.cons head tail)) :
    TraceProgramAssignment dynamics inertia tail := by
  cases assignment with
  | cons headAssignment tailAssignment => exact tailAssignment

noncomputable def TraceProgramAssignment.append
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    {left : Cordis.GlobalCalculus.Trace dynamics inertia start middle}
    {right : Cordis.GlobalCalculus.Trace dynamics inertia middle finish}
    (leftAssignment : TraceProgramAssignment dynamics inertia left)
    (rightAssignment : TraceProgramAssignment dynamics inertia right) :
    TraceProgramAssignment dynamics inertia
      (Cordis.GlobalTraceFacts.Trace.append left right) := by
  induction leftAssignment with
  | nil => exact rightAssignment
  | cons headAssignment tailAssignment ih => exact .cons headAssignment (ih rightAssignment)

structure AssignedAdjacentSwap
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (normal : StepPair dynamics inertia before after)
    extends ExactAdjacentSwap normal where
  swappedFirstAssignment :
    StepProgramAssignment toExactAdjacentSwap.swapped.first
  swappedSecondAssignment :
    StepProgramAssignment toExactAdjacentSwap.swapped.second

structure AssignedAdjacentOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace) where
  beforeAssignment : TraceProgramAssignment dynamics inertia occurrence.beforeTrace
  firstAssignment : StepProgramAssignment occurrence.pair.first
  secondAssignment : StepProgramAssignment occurrence.pair.second
  afterAssignment : TraceProgramAssignment dynamics inertia occurrence.afterTrace

noncomputable def AssignedAdjacentOccurrence.sourceAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence trace}
    (assigned : AssignedAdjacentOccurrence occurrence) :
    TraceProgramAssignment dynamics inertia trace := by
  let windowAndAfter : TraceProgramAssignment dynamics inertia
      (.cons occurrence.pair.first (.cons occurrence.pair.second occurrence.afterTrace)) :=
    .cons assigned.firstAssignment (.cons assigned.secondAssignment assigned.afterAssignment)
  let decomposed := TraceProgramAssignment.append assigned.beforeAssignment windowAndAfter
  rw [occurrence.decomposition]
  exact decomposed

noncomputable def AssignedAdjacentOccurrence.rewrittenAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence trace}
    (assigned : AssignedAdjacentOccurrence occurrence)
    (swap : AssignedAdjacentSwap occurrence.pair) :
    TraceProgramAssignment dynamics inertia
      (occurrence.rewrite swap.toExactAdjacentSwap) := by
  let windowAndAfter : TraceProgramAssignment dynamics inertia
      (.cons swap.swapped.first (.cons swap.swapped.second occurrence.afterTrace)) :=
    .cons swap.swappedFirstAssignment
      (.cons swap.swappedSecondAssignment assigned.afterAssignment)
  exact TraceProgramAssignment.append assigned.beforeAssignment windowAndAfter

/-! ## Concrete activation rule coherence -/

theorem reframeActivation_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (original : ProgramAlignedLandingActivation program origin)
    {baseState : State catalog Ambient}
    {baseStep : IterationStep dynamics program.owner original.code baseState}
    {foreignName : sig.Name} {foreignFiber : Fiber catalog}
    {foreignPhase : Phase (catalog.declaration foreignFiber.component)}
    (framed : Cordis.GlobalForeignPhase.PhaseFramedExecution program baseStep
      foreignName foreignFiber foreignPhase)
    (sourcePresent :
      (setPhase baseState foreignName foreignFiber foreignPhase).registry
        program.owner = some original.fiber)
    (targetMoved :
      targetView (setPhase baseState foreignName foreignFiber foreignPhase)
        program.owner original.fiber = some original.committed)
    (afterPresent : framed.movedStep.after.registry program.owner =
      some original.landing.afterFiber)
    (rawExact : Cordis.GlobalTransposition.LifecycleYieldAgrees
      baseStep original.landing.step) :
    (reframeActivation original framed sourcePresent targetMoved afterPresent
      rawExact).activation.rule = original.rule := by
  cases original with
  | mk fiber present code undos committed phase target landing witness outcome =>
      cases outcome <;> rfl

theorem program_activation_diamond_right_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws left right) :
    (program_activation_diamond (inertia := inertia) originWf different
      left right laws).rightAfterLeft.rule = right.rule := by
  cases left with
  | begin leftFiber leftGuard leftRoot =>
      cases right with
      | begin => rfl
      | landing rightAligned =>
          exact reframeActivation_rule_eq rightAligned _ _ _ _ _
  | landing leftAligned =>
      cases right with
      | begin => rfl
      | landing rightAligned =>
          exact reframeActivation_rule_eq rightAligned _ _ _ _ _

private theorem program_activation_diamond_left_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws left right) :
    (program_activation_diamond (inertia := inertia) originWf different
      left right laws).leftAfterRight.rule = left.rule := by
  cases left with
  | begin leftFiber leftGuard leftRoot =>
      cases right with
      | begin => rfl
      | landing => rfl
  | landing leftAligned =>
      cases right with
      | begin => exact reframeActivation_rule_eq leftAligned _ _ _ _ _
      | landing => exact reframeActivation_rule_eq leftAligned _ _ _ _ _

theorem transpose_program_activations_left_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws leftAtOrigin rightAtOrigin) :
    (transpose_program_activations (inertia := inertia) originWf different
      leftAtOrigin rightAfterLeft rightAtOrigin laws).leftAfterRight.rule =
        leftAtOrigin.rule :=
  program_activation_diamond_left_rule_eq originWf different
    leftAtOrigin rightAtOrigin laws

theorem transpose_program_activations_right_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws leftAtOrigin rightAtOrigin) :
    rightAtOrigin.rule = rightAfterLeft.rule := by
  let diamond := program_activation_diamond (inertia := inertia) originWf different
    leftAtOrigin rightAtOrigin laws
  calc
    rightAtOrigin.rule = diamond.rightAfterLeft.rule :=
      (program_activation_diamond_right_rule_eq originWf different
        leftAtOrigin rightAtOrigin laws).symm
    _ = rightAfterLeft.rule := diamond.rightAfterLeft.rule_unique rightAfterLeft

theorem lifecycleStep_transport
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before leftAfter rightAfter : State catalog Ambient}
    (equal : leftAfter = rightAfter)
    (transition : Transition dynamics inertia before leftAfter) :
    Step.lifecycle (equal ▸ transition) =
      transportStepAfter equal (Step.lifecycle transition) := by
  cases equal
  rfl

theorem transportStepAfter_trans
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before first second third : State catalog Ambient}
    (left : first = second) (right : second = third)
    (step : Step dynamics inertia before first) :
    transportStepAfter right (transportStepAfter left step) =
      transportStepAfter (left.trans right) step := by
  cases left
  cases right
  rfl

theorem swappedTransition_globalStep_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin final : State catalog Ambient}
    {leftAtOrigin : ProgramActivation leftProgram origin}
    {rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after}
    {rightAtOrigin : ProgramActivation rightProgram origin}
    (result : ProgramActivationTransposition leftAtOrigin rightAfterLeft rightAtOrigin)
    (finalEq : rightAfterLeft.after = final) :
    transportStepAfter finalEq (Step.lifecycle result.swappedTransition) =
      transportStepAfter (result.endpoint_eq.trans finalEq)
        (ProgramActivation.globalStep (inertia := inertia) result.leftAfterRight) := by
  calc
    transportStepAfter finalEq (Step.lifecycle result.swappedTransition) =
        transportStepAfter finalEq
          (transportStepAfter result.endpoint_eq
            (ProgramActivation.globalStep (inertia := inertia) result.leftAfterRight)) := by
      apply congrArg (transportStepAfter finalEq)
      exact lifecycleStep_transport result.endpoint_eq _
    _ = _ := transportStepAfter_trans result.endpoint_eq finalEq _

/-! ## Concrete activation/orchestration rule coherence -/

def liftOrchestrationKind : Cordis.GlobalVestigial.OrchestrationKind →
    Cordis.GlobalCalculus.Rule
  | .insert => .oInsert
  | .retire => .oRetire
  | .remove => .oRemove

def orchestrationGlobalStep
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    Step dynamics inertia before after :=
  .orchestration step

@[simp] theorem orchestrationGlobalStep_rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) step).rule =
      liftOrchestrationKind (Cordis.GlobalVestigial.orchestrationKind step) := by
  cases step <;> rfl

@[simp] theorem orchestrationGlobalStep_actor
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) step).actor =
      Actor.fiber (Cordis.GlobalVestigial.orchestrationName step) := by
  cases step <;> rfl

theorem sameOrchestrationTemplate_global_tags
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {left : OrchestrationStep leftBefore leftAfter}
    {right : OrchestrationStep rightBefore rightAfter}
    (same : SameOrchestrationTemplate left right) :
    (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) left).rule =
        (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) right).rule ∧
      (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) left).actor =
        (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia) right).actor := by
  constructor
  · rw [orchestrationGlobalStep_rule, orchestrationGlobalStep_rule]
    exact congrArg liftOrchestrationKind same.same_kind
  · rw [orchestrationGlobalStep_actor, orchestrationGlobalStep_actor,
      same.same_actor]

theorem transpose_activation_orchestration_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {inertia : InertiaPolicy dynamics} {origin final : State catalog Ambient}
    (originWf : WellFormed origin)
    (activation : Cordis.GlobalActivationTransposition.ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final)
    (different : program.owner ≠ Cordis.GlobalVestigial.orchestrationName normal)
    (laws : ActivationOrchestrationSwapLaws activation normal) :
    let result := transpose_activation_orchestration inertia originWf activation normal
      different laws
    result.activationSecond.rule = activation.rule := by
  cases activation with
  | begin => rfl
  | landing aligned =>
      cases aligned with
      | mk fiber present code undos committed phase target landing witness outcome =>
          cases outcome <;> rfl

def transportOrchestrationBefore
    {before left right : State catalog Ambient}
    (equal : left = right) (step : OrchestrationStep left before) :
    OrchestrationStep right before := by
  subst right
  exact step

@[simp] theorem transportOrchestrationBefore_kind
    {before left right : State catalog Ambient}
    (equal : left = right) (step : OrchestrationStep left before) :
    Cordis.GlobalVestigial.orchestrationKind (transportOrchestrationBefore equal step) =
      Cordis.GlobalVestigial.orchestrationKind step := by
  cases equal
  rfl

@[simp] theorem transportOrchestrationBefore_name
    {before left right : State catalog Ambient}
    (equal : left = right) (step : OrchestrationStep left before) :
    Cordis.GlobalVestigial.orchestrationName (transportOrchestrationBefore equal step) =
      Cordis.GlobalVestigial.orchestrationName step := by
  cases equal
  rfl

/-! ## Activation/activation actual-pair adapter -/

def transportProgramActivationSource
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {left right : State catalog Ambient} (equal : left = right)
    (activation : ProgramActivation program right) : ProgramActivation program left :=
  equal.symm ▸ activation

@[simp] theorem transportProgramActivationSource_after
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {left right : State catalog Ambient} (equal : left = right)
    (activation : ProgramActivation program right) :
    (transportProgramActivationSource equal activation).after = activation.after := by
  cases equal
  rfl

@[simp] theorem transportProgramActivationSource_rule
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {left right : State catalog Ambient} (equal : left = right)
    (activation : ProgramActivation program right) :
    (transportProgramActivationSource equal activation).rule = activation.rule := by
  cases equal
  rfl

noncomputable def transposeActivationPair
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {origin final : State catalog Ambient}
    (normal : StepPair dynamics inertia origin final)
    (leftAtOrigin : ProgramOccurrence normal.first)
    (rightAfterLeft : ProgramOccurrence normal.second)
    (rightAtOrigin : ProgramActivation rightAfterLeft.program origin)
    (originWf : WellFormed origin)
    (different : leftAtOrigin.program.owner ≠ rightAfterLeft.program.owner)
    (laws : ActivationSwapLaws leftAtOrigin.activation rightAtOrigin) :
    AssignedAdjacentSwap normal := by
  let transportedRight : ProgramActivation rightAfterLeft.program
      leftAtOrigin.activation.after :=
    transportProgramActivationSource leftAtOrigin.after_eq rightAfterLeft.activation
  have transportedFinal : transportedRight.after = final :=
    (transportProgramActivationSource_after leftAtOrigin.after_eq
      rightAfterLeft.activation).trans rightAfterLeft.after_eq
  let result := transpose_program_activations (inertia := inertia) originWf different
    leftAtOrigin.activation transportedRight rightAtOrigin laws
  let movedActivation : Step dynamics inertia rightAtOrigin.after final :=
    transportStepAfter (result.endpoint_eq.trans transportedFinal)
      (ProgramActivation.globalStep (inertia := inertia) result.leftAfterRight)
  let swapped : StepPair dynamics inertia origin final := {
    middle := rightAtOrigin.after
    first := ProgramActivation.globalStep (inertia := inertia) rightAtOrigin
    second := movedActivation
  }
  have rightRule : rightAtOrigin.rule = transportedRight.rule :=
    transpose_program_activations_right_rule_eq (inertia := inertia) originWf different
      leftAtOrigin.activation transportedRight rightAtOrigin laws
  have leftRule : result.leftAfterRight.rule = leftAtOrigin.activation.rule :=
    transpose_program_activations_left_rule_eq (inertia := inertia) originWf different
      leftAtOrigin.activation transportedRight rightAtOrigin laws
  have rightOriginal : rightAtOrigin.rule = rightAfterLeft.activation.rule :=
    rightRule.trans (transportProgramActivationSource_rule leftAtOrigin.after_eq _)
  let exactSwap : ExactAdjacentSwap normal := {
    swapped := swapped
    first_rule := by
      exact (ProgramActivation.globalStep_rule_eq_of_rule_eq rightOriginal).trans
        rightAfterLeft.rule_eq.symm
    second_rule := by
      calc
        swapped.second.rule =
            (ProgramActivation.globalStep (inertia := inertia)
              result.leftAfterRight).rule :=
          transportStepAfter_rule _ _
        _ = (ProgramActivation.globalStep (inertia := inertia)
              leftAtOrigin.activation).rule :=
          ProgramActivation.globalStep_rule_eq_of_rule_eq leftRule
        _ = normal.first.rule := leftAtOrigin.rule_eq.symm
    first_actor := by
      calc
        swapped.first.actor = Actor.fiber rightAfterLeft.program.owner :=
          ProgramActivation.globalStep_actor rightAtOrigin
        _ = normal.second.actor := congrArg Actor.fiber rightAfterLeft.actor_eq.symm
    second_actor := by
      calc
        swapped.second.actor =
            (ProgramActivation.globalStep (inertia := inertia)
              result.leftAfterRight).actor := transportStepAfter_actor _ _
        _ = Actor.fiber leftAtOrigin.program.owner :=
          ProgramActivation.globalStep_actor result.leftAfterRight
        _ = normal.first.actor := congrArg Actor.fiber leftAtOrigin.actor_eq.symm
  }
  exact {
    toExactAdjacentSwap := exactSwap
    swappedFirstAssignment := StepProgramAssignment.ofActivation rightAtOrigin
    swappedSecondAssignment := StepProgramAssignment.ofTransportedActivation
      result.leftAfterRight (result.endpoint_eq.trans transportedFinal)
  }

noncomputable def transposeActivationOrchestrationPair
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {origin final : State catalog Ambient}
    (normal : StepPair dynamics inertia origin final)
    (activation : ProgramOccurrence normal.first)
    (orchestration : OrchestrationOccurrence normal.second)
    (originWf : WellFormed origin)
    (different : activation.program.owner ≠
      Cordis.GlobalVestigial.orchestrationName
        (transportOrchestrationBefore activation.after_eq.symm orchestration.orchestration))
    (laws : ActivationOrchestrationSwapLaws activation.activation
      (transportOrchestrationBefore activation.after_eq.symm orchestration.orchestration)) :
    AssignedAdjacentSwap normal := by
  let transported :=
    transportOrchestrationBefore activation.after_eq.symm orchestration.orchestration
  let result := transpose_activation_orchestration inertia originWf activation.activation
    transported different laws
  let movedActivation : Step dynamics inertia result.orchestrationFirstState final :=
    transportStepAfter result.endpoint_eq
      (ProgramActivation.globalStep (inertia := inertia) result.activationSecond)
  let swapped : StepPair dynamics inertia origin final := {
    middle := result.orchestrationFirstState
    first := orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia)
      result.orchestrationFirst
    second := movedActivation
  }
  have sameTags := sameOrchestrationTemplate_global_tags
    (dynamics := dynamics) (inertia := inertia) result.same_template
  have movedRule := transpose_activation_orchestration_rule_eq
    (inertia := inertia) originWf activation.activation transported different laws
  let exactSwap : ExactAdjacentSwap normal := {
    swapped := swapped
    first_rule := by
      calc
        swapped.first.rule =
            (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia)
              transported).rule := sameTags.1
        _ = (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia)
              orchestration.orchestration).rule := by
            rw [orchestrationGlobalStep_rule, orchestrationGlobalStep_rule,
              transportOrchestrationBefore_kind]
        _ = normal.second.rule :=
          (congrArg Step.rule orchestration.step_eq).symm
    second_rule := by
      calc
        swapped.second.rule =
            (ProgramActivation.globalStep (inertia := inertia)
              result.activationSecond).rule :=
          transportStepAfter_rule result.endpoint_eq _
        _ = (ProgramActivation.globalStep (inertia := inertia)
              activation.activation).rule :=
          ProgramActivation.globalStep_rule_eq_of_rule_eq movedRule
        _ = normal.first.rule := activation.rule_eq.symm
    first_actor := by
      calc
        swapped.first.actor =
            (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia)
              transported).actor := sameTags.2
        _ = (orchestrationGlobalStep (dynamics := dynamics) (inertia := inertia)
              orchestration.orchestration).actor := by
          rw [orchestrationGlobalStep_actor, orchestrationGlobalStep_actor,
            transportOrchestrationBefore_name]
        _ = normal.second.actor :=
          (congrArg Step.actor orchestration.step_eq).symm
    second_actor := by
      calc
        swapped.second.actor =
            (ProgramActivation.globalStep (inertia := inertia)
              result.activationSecond).actor :=
          transportStepAfter_actor result.endpoint_eq _
        _ = Actor.fiber activation.program.owner :=
          ProgramActivation.globalStep_actor result.activationSecond
        _ = normal.first.actor := congrArg Actor.fiber activation.actor_eq.symm
  }
  exact {
    toExactAdjacentSwap := exactSwap
    swappedFirstAssignment :=
      StepProgramAssignment.ofOrchestration result.orchestrationFirst
    swappedSecondAssignment :=
      StepProgramAssignment.ofTransportedActivation result.activationSecond result.endpoint_eq
  }

/-! ## Whole-trace semantic adapters -/

noncomputable def transposeActivationOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (leftAtOrigin : ProgramOccurrence occurrence.pair.first)
    (rightAfterLeft : ProgramOccurrence occurrence.pair.second)
    (rightAtOrigin : Cordis.GlobalActivationTransposition.ProgramActivation
      rightAfterLeft.program occurrence.windowStart)
    (initialWf : WellFormed initial)
    (different : leftAtOrigin.program.owner ≠ rightAfterLeft.program.owner)
    (laws : ActivationSwapLaws leftAtOrigin.activation rightAtOrigin) :
    AssignedAdjacentSwap occurrence.pair :=
  transposeActivationPair occurrence.pair leftAtOrigin rightAfterLeft rightAtOrigin
    (occurrence.beforeTrace.preservesWellFormed initialWf) different laws

noncomputable def rewriteActivationOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (leftAtOrigin : ProgramOccurrence occurrence.pair.first)
    (rightAfterLeft : ProgramOccurrence occurrence.pair.second)
    (rightAtOrigin : Cordis.GlobalActivationTransposition.ProgramActivation
      rightAfterLeft.program occurrence.windowStart)
    (initialWf : WellFormed initial)
    (different : leftAtOrigin.program.owner ≠ rightAfterLeft.program.owner)
    (laws : ActivationSwapLaws leftAtOrigin.activation rightAtOrigin) :
    Cordis.GlobalCalculus.Trace dynamics inertia initial final :=
  occurrence.rewrite (transposeActivationOccurrence occurrence leftAtOrigin rightAfterLeft
    rightAtOrigin initialWf different laws).toExactAdjacentSwap

noncomputable def transposeActivationOrchestrationOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (activation : ProgramOccurrence occurrence.pair.first)
    (orchestration : OrchestrationOccurrence occurrence.pair.second)
    (initialWf : WellFormed initial)
    (different : activation.program.owner ≠
      Cordis.GlobalVestigial.orchestrationName
        (transportOrchestrationBefore activation.after_eq.symm
          orchestration.orchestration))
    (laws : ActivationOrchestrationSwapLaws activation.activation
      (transportOrchestrationBefore activation.after_eq.symm
        orchestration.orchestration)) :
    AssignedAdjacentSwap occurrence.pair :=
  transposeActivationOrchestrationPair occurrence.pair activation orchestration
    (occurrence.beforeTrace.preservesWellFormed initialWf) different laws

noncomputable def rewriteActivationOrchestrationOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {trace : Cordis.GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence trace)
    (activation : ProgramOccurrence occurrence.pair.first)
    (orchestration : OrchestrationOccurrence occurrence.pair.second)
    (initialWf : WellFormed initial)
    (different : activation.program.owner ≠
      Cordis.GlobalVestigial.orchestrationName
        (transportOrchestrationBefore activation.after_eq.symm
          orchestration.orchestration))
    (laws : ActivationOrchestrationSwapLaws activation.activation
      (transportOrchestrationBefore activation.after_eq.symm
        orchestration.orchestration)) :
    Cordis.GlobalCalculus.Trace dynamics inertia initial final :=
  occurrence.rewrite (transposeActivationOrchestrationOccurrence occurrence activation
    orchestration initialWf different laws).toExactAdjacentSwap

/-! ## Nonempty-context executable evidence -/

namespace Example

namespace ActivationPair

open Cordis.GlobalActivationTransposition.Example.BeginPairs

abbrev dynamics := Cordis.GlobalLandingTransposition.Example.dynamics
abbrev inertia := Cordis.GlobalLandingTransposition.Example.inertia
abbrev origin := beginOrigin

noncomputable def normalPair : StepPair dynamics inertia origin
    beginBeginDiamond.rightAfterLeft.after where
  middle := beginLeft.after
  first := ProgramActivation.globalStep beginLeft
  second := ProgramActivation.globalStep beginBeginDiamond.rightAfterLeft

noncomputable def leftOccurrence : ProgramOccurrence normalPair.first :=
  ProgramOccurrence.ofActivation beginLeft

noncomputable def rightOccurrence : ProgramOccurrence normalPair.second :=
  ProgramOccurrence.ofActivation beginBeginDiamond.rightAfterLeft

noncomputable def windowAssignment : TraceProgramAssignment dynamics inertia normalPair.trace :=
  .cons (StepProgramAssignment.ofActivation beginLeft)
    (.cons (StepProgramAssignment.ofActivation beginBeginDiamond.rightAfterLeft)
      (.nil normalPair.secondRecord.after))

noncomputable def extractedLeftOccurrence : ProgramOccurrence normalPair.first :=
  windowAssignment.headOccurrence (by trivial)

noncomputable def extractedRightOccurrence : ProgramOccurrence normalPair.second := by
  exact windowAssignment.tail.headOccurrence (by trivial)

theorem extractedLeftOccurrence_eq : extractedLeftOccurrence = leftOccurrence := by
  unfold extractedLeftOccurrence windowAssignment
  rfl

theorem extractedRightOccurrence_eq : extractedRightOccurrence = rightOccurrence := by
  unfold extractedRightOccurrence windowAssignment
  rfl

noncomputable def assignedSwap : AssignedAdjacentSwap normalPair := by
  have leftEq := extractedLeftOccurrence_eq
  have rightEq := extractedRightOccurrence_eq
  cases leftEq
  cases rightEq
  exact transposeActivationPair normalPair extractedLeftOccurrence extractedRightOccurrence
    beginRight
    beginOrigin_wellFormed (by decide) beginBeginLaws

theorem swapped_rules : assignedSwap.swapped.rules = [.lBegin, .lBegin] := by
  change [assignedSwap.swapped.first.rule, assignedSwap.swapped.second.rule] = _
  rw [assignedSwap.first_rule, assignedSwap.second_rule]
  rfl

theorem swapped_actors : assignedSwap.swapped.actors =
    [.fiber true, .fiber false] := by
  change [assignedSwap.swapped.first.actor, assignedSwap.swapped.second.actor] = _
  rw [assignedSwap.first_actor, assignedSwap.second_actor]
  rfl

end ActivationPair

namespace ActivationOrchestration

open Cordis.GlobalActivationOrchestrationTransposition.BeginInsert

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia
abbrev origin := Cordis.GlobalLifecycle.Example.start
abbrev initial := Cordis.GlobalCalculus.Example.emptyStart

def normalPair : StepPair dynamics inertia origin final where
  middle := activation.after
  first := ProgramActivation.globalStep activation
  second := orchestrationGlobalStep normal

def activationOccurrence : ProgramOccurrence normalPair.first :=
  ProgramOccurrence.ofActivation activation

def orchestrationOccurrence : OrchestrationOccurrence normalPair.second :=
  OrchestrationOccurrence.ofOrchestration normal

noncomputable def assignedSwap : AssignedAdjacentSwap normalPair :=
  transposeActivationOrchestrationPair normalPair activationOccurrence
    orchestrationOccurrence Cordis.GlobalLifecycle.Example.start_wellFormed (by decide) laws

def beforeTrace : Cordis.GlobalCalculus.Trace dynamics inertia initial origin :=
  .cons Cordis.GlobalCalculus.Example.insertStep (.nil origin)

def sourceTrace : Cordis.GlobalCalculus.Trace dynamics inertia initial final :=
  Cordis.GlobalTraceFacts.Trace.append beforeTrace
    (.cons normalPair.first (.cons normalPair.second (.nil final)))

def occurrence : AdjacentOccurrence sourceTrace where
  windowStart := origin
  windowEnd := final
  beforeTrace := beforeTrace
  pair := normalPair
  afterTrace := .nil final
  decomposition := rfl

def beforeAssignment : TraceProgramAssignment dynamics inertia beforeTrace :=
  .cons (StepProgramAssignment.ofOrchestration
    Cordis.GlobalCalculus.Example.insertTransition) (.nil origin)

def assignedOccurrence : AssignedAdjacentOccurrence occurrence where
  beforeAssignment := beforeAssignment
  firstAssignment := StepProgramAssignment.ofActivation activation
  secondAssignment := StepProgramAssignment.ofOrchestration normal
  afterAssignment := .nil final

def windowAssignment : TraceProgramAssignment dynamics inertia
    (.cons normalPair.first (.cons normalPair.second (.nil final))) :=
  .cons assignedOccurrence.firstAssignment
    (.cons assignedOccurrence.secondAssignment (.nil final))

def extractedActivationOccurrence : ProgramOccurrence normalPair.first :=
  windowAssignment.headOccurrence (by trivial)

theorem extracted_activation_is_fixed_program :
    extractedActivationOccurrence.program = activationOccurrence.program := rfl

noncomputable def ledgerAssignedSwap : AssignedAdjacentSwap normalPair :=
  transposeActivationOrchestrationPair normalPair extractedActivationOccurrence
    orchestrationOccurrence Cordis.GlobalLifecycle.Example.start_wellFormed (by decide) laws

noncomputable def rewritten : Cordis.GlobalCalculus.Trace dynamics inertia initial final :=
  occurrence.rewrite ledgerAssignedSwap.toExactAdjacentSwap

noncomputable def sourceAssignment : TraceProgramAssignment dynamics inertia sourceTrace :=
  assignedOccurrence.sourceAssignment

noncomputable def rewrittenAssignment : TraceProgramAssignment dynamics inertia rewritten :=
  assignedOccurrence.rewrittenAssignment ledgerAssignedSwap

theorem retained_context_nonempty : beforeTrace.rules = [.oInsert] := rfl

theorem source_rules : sourceTrace.rules = [.oInsert, .lBegin, .oInsert] := rfl

theorem rewritten_rules : rewritten.rules = [.oInsert, .oInsert, .lBegin] := by
  exact occurrence.rewrite_rules ledgerAssignedSwap.toExactAdjacentSwap

theorem rewritten_actors : rewritten.actors =
    [.fiber 0, .fiber 1, .fiber 0] := by
  exact occurrence.rewrite_actors ledgerAssignedSwap.toExactAdjacentSwap

def executableProjection : List Cordis.GlobalCalculus.Rule × List Nat :=
  ([.oInsert, .oInsert, .lBegin], [0, 1, 0])

theorem rewritten_projection :
    (rewritten.rules, rewritten.actors.map fun actor => match actor with
      | .fiber name => name) = executableProjection := by
  rw [rewritten_rules, rewritten_actors]
  rfl

end ActivationOrchestration

end Example

/-! ## Explicit bridges to the retained counterexample boundary -/

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap

theorem registering_insert_parent_gap :
    (∃ fiber, registered.registry 1 = some fiber) ∧
      ¬(∃ fiber, Source.registry 1 = some fiber) :=
  parent_adoption_blocks_early_insert

theorem registering_insert_birth_gap :
    normal ≠ swapped :=
  registration_insert_birth_order_differs

theorem bare_landing_has_no_unique_program :
    ¬LandingProgramWitness
      Cordis.GlobalLandingTransposition.OracleProvenanceGap.programOne
      Cordis.GlobalLandingTransposition.OracleProvenanceGap.landingTwo :=
  Cordis.GlobalActivationTransposition.bare_landing_does_not_determine_program

end Cordis.GlobalTraceRewrite
