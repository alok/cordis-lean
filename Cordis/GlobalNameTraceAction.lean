import Cordis.GlobalNameLifecycle
import Cordis.GlobalTraceRewrite

/-!
# Conditional name action on complete global traces

This module lifts the existing conditional name-equivariance laws from one unified global step
to an intrinsic dependent trace. It transports exact endpoints, strengthened well-formedness,
rule lists, actor lists, and per-occurrence program assignments.

The trace action is exact at the acted endpoints and is conditional in two separate ways. Source
well-formedness is required by the lifecycle action, and activation occurrences require an explicit
program/landing transport certificate. The latter is deliberately supplied rather than inferred:
the current APIs do not identify an arbitrary lifecycle landing with a unique fixed program,
registration oracle, or reachable continuation. Orchestration and non-activation lifecycle
assignments are reconstructed directly.

This is a finite trace-level analogue of the name-equivariance part of paper Lemma 56. It does
not claim unconditional lifecycle bisimulation, birth-erased endpoint equality, or the paper's
full Lemmas 71--73.
-/

set_option autoImplicit false

namespace Cordis.GlobalNameTraceAction

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
  Cordis.GlobalCalculus Cordis.GlobalNameAction Cordis.GlobalNameLifecycle
  Cordis.GlobalIteratorIndependence Cordis.GlobalTraceRewrite

universe u
variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

def actStep
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : Step dynamics inertia before after) :
    Step dynamics inertia (actState action before) (actState action after) :=
  (actUnifiedStep assumptions beforeWf step).acted

theorem actStep_rule
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : Step dynamics inertia before after) :
    (actStep assumptions beforeWf step).rule = step.rule :=
  (actUnifiedStep assumptions beforeWf step).same_rule

theorem actStep_name
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : Step dynamics inertia before after) :
    (actStep assumptions beforeWf step).actedName = action.name step.actedName :=
  (actUnifiedStep assumptions beforeWf step).acted_name

def actTrace
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before) :
    GlobalCalculus.Trace dynamics inertia before after →
      GlobalCalculus.Trace dynamics inertia (actState action before) (actState action after)
  | .nil state => .nil (actState action state)
  | .cons head tail =>
      .cons (actStep assumptions beforeWf head)
        (actTrace assumptions (head.preservesWellFormed beforeWf) tail)

theorem actTrace_rules
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    (actTrace assumptions beforeWf trace).rules = trace.rules := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [actTrace, Cordis.GlobalCalculus.Trace.rules]
      rw [actStep_rule assumptions beforeWf head, ih]

def mapActor (action : NameAction sig Ambient) : Actor sig.Name → Actor sig.Name
  | .fiber name => .fiber (action.name name)

theorem actStep_actor
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : Step dynamics inertia before after) :
    (actStep assumptions beforeWf step).actor = mapActor action step.actor := by
  change Actor.fiber (actStep assumptions beforeWf step).actedName =
    mapActor action (Actor.fiber step.actedName)
  simpa [mapActor] using congrArg Actor.fiber (actStep_name assumptions beforeWf step)

theorem actTrace_actors
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    (actTrace assumptions beforeWf trace).actors = trace.actors.map (mapActor action) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [actTrace, Cordis.GlobalCalculus.Trace.actors, List.map_cons]
      rw [actStep_actor assumptions beforeWf head, ih]

def actProgram
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (program : Program dynamics) : Program dynamics where
  owner := action.name program.owner
  RegistrationError := program.RegistrationError
  oracle := actRegistrationOracle equivariant program.oracle
  root := action.iterator program.root

@[simp] theorem actProgram_owner
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (program : Program dynamics) :
    (actProgram equivariant program).owner = action.name program.owner := rfl

@[simp] theorem actProgram_root
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (program : Program dynamics) :
    (actProgram equivariant program).root = action.iterator program.root := rfl

structure ProgramOccurrenceTransport
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    {step : Step dynamics inertia before after}
    (source : ProgramOccurrence step) where
  activation :
    Cordis.GlobalActivationTransposition.ProgramActivation
      (actProgram assumptions.dynamics_equivariant source.program)
      (actState action before)
  after_eq : activation.after = actState action after
  step_eq : actStep assumptions beforeWf step =
    after_eq ▸ ProgramActivation.globalStep (inertia := inertia) activation
  rule_eq : activation.rule = source.activation.rule

def ProgramOccurrenceTransport.toOccurrence
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {assumptions : NameLifecycleAssumptions action dynamics inertia}
    {before after : State catalog Ambient} {beforeWf : WellFormed before}
    {step : Step dynamics inertia before after}
    (source : ProgramOccurrence step)
    (transport : ProgramOccurrenceTransport assumptions beforeWf source) :
    ProgramOccurrence (actStep assumptions beforeWf step) where
  program := actProgram assumptions.dynamics_equivariant source.program
  activation := transport.activation
  after_eq := transport.after_eq
  step_eq := transport.step_eq

structure ActivationAssignmentTransport
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia) where
  transport : ∀ {before after : State catalog Ambient}
    (beforeWf : WellFormed before)
    {step : Step dynamics inertia before after}
    {_activationRule : IsProgramActivationRule step.rule}
    (source : ProgramOccurrence step),
    ProgramOccurrenceTransport assumptions beforeWf source

noncomputable def actStepAssignment
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (activationTransport : ActivationAssignmentTransport assumptions)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    {step : Step dynamics inertia before after}
    (assignment : StepProgramAssignment step) :
    StepProgramAssignment (actStep assumptions beforeWf step) := by
  by_cases activationRule : IsProgramActivationRule step.rule
  · refine { occurrence := ?_ }
    intro _
    exact (activationTransport.transport (_activationRule := activationRule) beforeWf
      (assignment.occurrence activationRule)).toOccurrence
  · exact StepProgramAssignment.ofNotActivation _ (by
      intro targetRule
      apply activationRule
      rw [← actStep_rule assumptions beforeWf step]
      exact targetRule)

def actOrchestrationAssignment
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : OrchestrationStep before after) :
    StepProgramAssignment (actStep assumptions beforeWf (.orchestration step)) := by
  exact StepProgramAssignment.ofOrchestration (actOrchestrationStep action step)

def actNonactivationLifecycleAssignment
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia before after)
    (notActivation : ¬IsProgramActivationRule
      (GlobalCalculus.Step.lifecycle transition).rule) :
    StepProgramAssignment (actStep assumptions beforeWf (.lifecycle transition)) := by
  exact StepProgramAssignment.ofNotActivation _ (by
    intro targetRule
    apply notActivation
    rw [← actStep_rule assumptions beforeWf (.lifecycle transition)]
    exact targetRule)

noncomputable def actTraceAssignment
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (activationTransport : ActivationAssignmentTransport assumptions)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (assignment : TraceProgramAssignment dynamics inertia trace) :
    TraceProgramAssignment dynamics inertia (actTrace assumptions beforeWf trace) := by
  cases trace with
  | nil _ => exact .nil _
  | cons head tail =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          exact .cons
            (actStepAssignment assumptions activationTransport beforeWf headAssignment)
            (actTraceAssignment assumptions activationTransport
              (head.preservesWellFormed beforeWf) tailAssignment)

structure AssignedForwardTrace
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient}
    (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (assignment : TraceProgramAssignment dynamics inertia trace)
    (activationTransport : ActivationAssignmentTransport assumptions) where
  acted : GlobalCalculus.Trace dynamics inertia (actState action before) (actState action after)
  acted_eq : acted = actTrace assumptions beforeWf trace
  actedAssignment : TraceProgramAssignment dynamics inertia (actTrace assumptions beforeWf trace) :=
    actTraceAssignment assumptions activationTransport beforeWf assignment
  rules_eq : (actTrace assumptions beforeWf trace).rules = trace.rules :=
    actTrace_rules assumptions beforeWf trace
  actors_eq : (actTrace assumptions beforeWf trace).actors = trace.actors.map (mapActor action) :=
    actTrace_actors assumptions beforeWf trace

theorem actTrace_preservesWellFormed
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    WellFormed (actState action after) :=
  (actTrace assumptions beforeWf trace).preservesWellFormed
    (wellFormed_act action beforeWf)

noncomputable def assignedForwardTrace
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (assignment : TraceProgramAssignment dynamics inertia trace)
    (activationTransport : ActivationAssignmentTransport assumptions) :
    AssignedForwardTrace assumptions beforeWf trace assignment activationTransport :=
  { acted := actTrace assumptions beforeWf trace
    acted_eq := rfl }

end Cordis.GlobalNameTraceAction
