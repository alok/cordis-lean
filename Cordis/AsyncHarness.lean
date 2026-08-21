import Cordis.ParallelHarness

/-!
# A bounded proof-carrying fiber scheduler

This module is the next runtime-facing slice after the pure parallel-window certificate.  It
reifies fiber phases and completion-order races, while keeping the model effect pure and indexed.
Starting, completing, failing, and cancelling a fiber are explicit typed transitions.  A
`SuccessfulSchedule` proves that a finite completion order is a permutation of the declared model
order, so the existing reversible-effect commutation theorem gives the exact final model state.

This is deliberately not a theorem about arbitrary `IO` task cancellation, wall-clock fairness,
or a deployed Harness runtime.  The `drained` field is a finite fairness certificate: every
declared fiber is terminal at the supplied endpoint.  An adapter may attach real task handles only
after proving that its observations satisfy this finite transition surface.
-/

namespace Cordis.AsyncHarness

open Cordis
open Cordis.ParallelHarness

universe u v

set_option autoImplicit false

/-- The lifecycle phase of one declared fiber. -/
inductive Phase (Result : Type v) where
  | pending
  | running
  | completed (value : Result)
  | failed (reason : String)
  | cancelled (reason : String)

namespace Phase

def isTerminal {Result : Type v} : Phase Result -> Bool
  | .pending | .running => false
  | .completed _ | .failed _ | .cancelled _ => true

theorem isTerminal_eq_true_of_completed
    {Result : Type v} (value : Result) : isTerminal (.completed value) = true := rfl

theorem isTerminal_eq_true_of_failed
    {Result : Type v} (reason : String) :
    isTerminal (.failed reason : Phase Result) = true := rfl

theorem isTerminal_eq_true_of_cancelled
    {Result : Type v} (reason : String) :
    isTerminal (.cancelled reason : Phase Result) = true := rfl

end Phase

/-- A finite family of pure proof-carrying calls with stable public IDs. -/
structure FiberPlan (State : Type u) (Result : Type v) where
  tasks : List (Task State Result)
  ids_nodup : (tasks.map Task.id).Nodup
  commuting : Schedule.CommutingFamily (tasks.map Task.effect)

namespace FiberPlan

variable {State : Type u} {Result : Type v}

def taskAt (plan : FiberPlan State Result) (index : Fin plan.tasks.length) :
    Task State Result := plan.tasks.get index

def canonicalEffect (plan : FiberPlan State Result) : Effect State :=
  Schedule.runEffects (plan.tasks.map Task.effect)

theorem taskAt_mem
    (plan : FiberPlan State Result) (index : Fin plan.tasks.length) :
    plan.taskAt index ∈ plan.tasks := by
  exact List.get_mem plan.tasks index

theorem canonical_effect_eq_of_perm
    (plan : FiberPlan State Result)
    {ordered : List (Task State Result)}
    (permutation : plan.tasks.map Task.effect = ordered.map Task.effect) :
    plan.canonicalEffect = Schedule.runEffects (ordered.map Task.effect) := by
  change Schedule.runEffects (plan.tasks.map Task.effect) =
    Schedule.runEffects (ordered.map Task.effect)
  rw [permutation]

end FiberPlan

/-- The indexed runtime state.  The task family is immutable; only phases and model state move. -/
structure Runtime
    {State : Type u} {Result : Type v}
    (plan : FiberPlan State Result) where
  phase : (index : Fin plan.tasks.length) -> Phase Result
  model : State

namespace Runtime

variable {State : Type u} {Result : Type v}
variable {plan : FiberPlan State Result}

def updatePhase
    (phase : (index : Fin plan.tasks.length) -> Phase Result)
    (index : Fin plan.tasks.length) (value : Phase Result) :
    (index : Fin plan.tasks.length) -> Phase Result :=
  fun other => if other = index then value else phase other

def initial (plan : FiberPlan State Result) (before : State) : Runtime plan where
  phase := fun _ => .pending
  model := before

def start (runtime : Runtime plan) (index : Fin plan.tasks.length) : Runtime plan :=
  { runtime with phase := updatePhase runtime.phase index .running }

def complete (runtime : Runtime plan) (index : Fin plan.tasks.length) : Runtime plan :=
  let task := plan.taskAt index
  let applied := task.effect runtime.model
  { phase := updatePhase runtime.phase index (.completed (task.result runtime.model))
    model := applied.after }

def fail
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) : Runtime plan :=
  { runtime with phase := updatePhase runtime.phase index (.failed reason) }

def cancel
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) : Runtime plan :=
  { runtime with phase := updatePhase runtime.phase index (.cancelled reason) }

def drained (runtime : Runtime plan) : Prop :=
  ∀ index, (runtime.phase index).isTerminal = true

@[simp]
theorem start_phase
    (runtime : Runtime plan) (index : Fin plan.tasks.length) :
    (runtime.start index).phase index = .running := by
  simp [Runtime.start, updatePhase]

@[simp]
theorem complete_phase
    (runtime : Runtime plan) (index : Fin plan.tasks.length) :
    (runtime.complete index).phase index =
      .completed ((plan.taskAt index).result runtime.model) := by
  simp [Runtime.complete, updatePhase]

@[simp]
theorem fail_phase
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) :
    (runtime.fail index reason).phase index = .failed reason := by
  simp [Runtime.fail, updatePhase]

@[simp]
theorem cancel_phase
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) :
    (runtime.cancel index reason).phase index = .cancelled reason := by
  simp [Runtime.cancel, updatePhase]

theorem start_model
    (runtime : Runtime plan) (index : Fin plan.tasks.length) :
    (runtime.start index).model = runtime.model := rfl

theorem fail_model
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) :
    (runtime.fail index reason).model = runtime.model := rfl

theorem cancel_model
    (runtime : Runtime plan) (index : Fin plan.tasks.length) (reason : String) :
    (runtime.cancel index reason).model = runtime.model := rfl

theorem update_phase_other
    (runtime : Runtime plan) (index other : Fin plan.tasks.length) (different : other ≠ index)
    (phase : Phase Result) :
    updatePhase runtime.phase index phase other = runtime.phase other := by
  simp [updatePhase, different]

end Runtime

/-! ## Typed one-fiber transitions -/

inductive Step
    {State : Type u} {Result : Type v}
    (plan : FiberPlan State Result) : Runtime plan -> Runtime plan -> Type
  | start
      {before : Runtime plan}
      (index : Fin plan.tasks.length)
      (phase_eq : before.phase index = .pending) :
      Step plan before (before.start index)
  | complete
      {before : Runtime plan}
      (index : Fin plan.tasks.length)
      (phase_eq : before.phase index = .running) :
      Step plan before (before.complete index)
  | fail
      {before : Runtime plan}
      (index : Fin plan.tasks.length)
      (reason : String)
      (phase_eq : before.phase index = .running) :
      Step plan before (before.fail index reason)
  | cancel
      {before : Runtime plan}
      (index : Fin plan.tasks.length)
      (reason : String)
      (phase_eq : before.phase index = .pending ∨ before.phase index = .running) :
      Step plan before (before.cancel index reason)

namespace Step

variable {State : Type u} {Result : Type v}
variable {plan : FiberPlan State Result}

def index {before after : Runtime plan} : Step plan before after -> Fin plan.tasks.length
  | .start index _ | .complete index _ | .fail index _ _ | .cancel index _ _ => index

inductive Kind where
  | start
  | complete
  | fail
  | cancel
deriving DecidableEq, Repr

def kind {before after : Runtime plan} : Step plan before after -> Kind
  | .start _ _ => .start
  | .complete _ _ => .complete
  | .fail _ _ _ => .fail
  | .cancel _ _ _ => .cancel

def reason {before after : Runtime plan} : Step plan before after -> Option String
  | .start _ _ | .complete _ _ => none
  | .fail _ reason _ | .cancel _ reason _ => some reason

def completedTask {before after : Runtime plan} :
    Step plan before after -> Option (Task State Result)
  | .start _ _ | .fail _ _ _ | .cancel _ _ _ => none
  | .complete index _ => some (plan.taskAt index)

theorem start_model_eq
    {before after : Runtime plan} (step : Step plan before after)
    (isStart : step.kind = .start) : after.model = before.model := by
  cases step with
  | start _ _ => rfl
  | complete _ _ => cases isStart
  | fail _ _ _ => cases isStart
  | cancel _ _ _ => cases isStart

theorem noncomplete_model_eq
    {before after : Runtime plan} (step : Step plan before after)
    (isNotComplete : step.kind ≠ .complete) : after.model = before.model := by
  cases step with
  | start _ _ => rfl
  | complete _ _ => exact False.elim (isNotComplete rfl)
  | fail _ _ _ => rfl
  | cancel _ _ _ => rfl

theorem complete_model_eq
    {before after : Runtime plan} (step : Step plan before after)
    (isComplete : step.kind = .complete) :
    after.model = ((plan.taskAt step.index).effect before.model).after := by
  cases step with
  | start _ _ => cases isComplete
  | complete _ _ => rfl
  | fail _ _ _ => cases isComplete
  | cancel _ _ _ => cases isComplete

theorem terminal_guard
    {before after : Runtime plan} (step : Step plan before after) :
    before.phase step.index = .pending ∨ before.phase step.index = .running := by
  cases step with
  | start _ phase_eq => exact Or.inl phase_eq
  | complete _ phase_eq => exact Or.inr phase_eq
  | fail _ _ phase_eq => exact Or.inr phase_eq
  | cancel _ _ phase_eq => exact phase_eq

theorem terminal_phase_of_complete
    {before after : Runtime plan} (step : Step plan before after)
    (isComplete : step.kind = .complete) :
    after.phase step.index =
      .completed ((plan.taskAt step.index).result before.model) := by
  cases step with
  | start _ _ => cases isComplete
  | complete index _ =>
      change Runtime.updatePhase before.phase index
          (.completed ((plan.taskAt index).result before.model)) index =
        .completed ((plan.taskAt index).result before.model)
      simp [Runtime.updatePhase]
  | fail _ _ _ => cases isComplete
  | cancel _ _ _ => cases isComplete

theorem terminal_phase_of_fail
    {before after : Runtime plan} (step : Step plan before after)
    (isFail : step.kind = .fail) : ∃ reason, after.phase step.index = .failed reason := by
  cases step with
  | start _ _ => cases isFail
  | complete _ _ => cases isFail
  | fail index reason _ =>
      refine ⟨reason, ?_⟩
      change Runtime.updatePhase before.phase index (.failed reason) index = _
      simp [Runtime.updatePhase]
  | cancel _ _ _ => cases isFail

theorem terminal_phase_of_cancel
    {before after : Runtime plan} (step : Step plan before after)
    (isCancel : step.kind = .cancel) : ∃ reason, after.phase step.index = .cancelled reason := by
  cases step with
  | start _ _ => cases isCancel
  | complete _ _ => cases isCancel
  | fail _ _ _ => cases isCancel
  | cancel index reason _ =>
      refine ⟨reason, ?_⟩
      change Runtime.updatePhase before.phase index (.cancelled reason) index = _
      simp [Runtime.updatePhase]

end Step

/-! ## Finite traces and completion-order certificates -/

inductive Trace
    {State : Type u} {Result : Type v}
    (plan : FiberPlan State Result) : Runtime plan -> Runtime plan -> Type (max (u + 1) (v + 1))
  | nil (state : Runtime plan) : Trace plan state state
  | cons
      {before middle after : Runtime plan}
      (head : Step plan before middle)
      (tail : Trace plan middle after) :
      Trace plan before after

namespace Trace

variable {State : Type u} {Result : Type v}
variable {plan : FiberPlan State Result}

def length {before after : Runtime plan} : Trace plan before after -> Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

def successful {before after : Runtime plan} : Trace plan before after -> Prop
  | .nil _ => True
  | .cons head tail =>
      (head.kind = .start ∨ head.kind = .complete) ∧ tail.successful

def completionTasks {before after : Runtime plan} :
    Trace plan before after -> List (Task State Result)
  | .nil _ => []
  | .cons head tail =>
      match head.completedTask with
      | none => tail.completionTasks
      | some task => task :: tail.completionTasks

def completionIds {before after : Runtime plan} (trace : Trace plan before after) : List Nat :=
  trace.completionTasks.map Task.id

theorem length_nil {state : Runtime plan} : (Trace.nil state).length = 0 := rfl

theorem length_cons
    {before middle after : Runtime plan}
    (head : Step plan before middle) (tail : Trace plan middle after) :
    (Trace.cons head tail).length = tail.length + 1 := rfl

theorem completionTasks_cons
    {before middle after : Runtime plan}
    (head : Step plan before middle) (tail : Trace plan middle after) :
    (Trace.cons head tail).completionTasks =
      match head.completedTask with
      | none => tail.completionTasks
      | some task => task :: tail.completionTasks := rfl

theorem model_eq_runEffects
    {before after : Runtime plan} (trace : Trace plan before after)
    (successful : trace.successful) :
    after.model =
      (Schedule.runEffects (trace.completionTasks.map Task.effect) before.model).after := by
  induction trace with
  | nil state => rfl
  | @cons before middle after head tail inductionHypothesis =>
      rcases successful with ⟨head_success, tail_success⟩
      cases head with
      | start index phase_eq =>
          simp only [Step.kind] at head_success
          have tail_model := inductionHypothesis tail_success
          change after.model =
            (Schedule.runEffects (tail.completionTasks.map Task.effect)
              (before.start index).model).after
          simpa [Runtime.start, Runtime.updatePhase] using tail_model
      | complete index phase_eq =>
          simp only [Step.kind] at head_success
          have tail_model := inductionHypothesis tail_success
          change after.model =
            (Schedule.runEffects
              ((plan.taskAt index :: tail.completionTasks).map Task.effect)
              before.model).after
          simpa [Runtime.complete, Runtime.updatePhase, Schedule.runEffects] using tail_model
      | fail index reason phase_eq =>
          have impossible : False := by
            rcases head_success with h | h <;> cases h
          exact impossible.elim
      | cancel index reason phase_eq =>
          have impossible : False := by
            rcases head_success with h | h <;> cases h
          exact impossible.elim

theorem no_completion_preserves_model
    {before after : Runtime plan} (trace : Trace plan before after)
    (successful : trace.successful)
    (none : trace.completionTasks = []) : after.model = before.model := by
  rw [trace.model_eq_runEffects successful, none]
  rfl

theorem completionIds_length
    {before after : Runtime plan} (trace : Trace plan before after) :
    trace.completionIds.length = trace.completionTasks.length := by
  simp [completionIds]

end Trace

/-! ## Draining and canonical endpoint -/

structure SuccessfulSchedule
    {State : Type u} {Result : Type v}
    (plan : FiberPlan State Result) (before : State) where
  final : Runtime plan
  trace : Trace plan (Runtime.initial plan before) final
  successful : trace.successful
  completion_permutation :
    (plan.tasks.map Task.effect).Perm (trace.completionTasks.map Task.effect)
  drained : final.drained

namespace SuccessfulSchedule

variable {State : Type u} {Result : Type v}
variable {plan : FiberPlan State Result} {before : State}

def canonicalEffect (_schedule : SuccessfulSchedule plan before) : Effect State :=
  plan.canonicalEffect

theorem final_model_eq_canonical
    (schedule : SuccessfulSchedule plan before) :
    schedule.final.model = (schedule.canonicalEffect before).after := by
  rw [Trace.model_eq_runEffects schedule.trace schedule.successful]
  exact congrArg (fun effect : Effect State => (effect before).after)
    (Schedule.runEffects_eq_of_perm schedule.completion_permutation
      plan.commuting).symm

theorem completion_ids_length
    (schedule : SuccessfulSchedule plan before) :
    schedule.trace.completionIds.length = schedule.trace.completionTasks.length :=
  schedule.trace.completionIds_length

end SuccessfulSchedule

/-! ## A concrete two-fiber completion race and cancellation witness -/

def examplePlan : FiberPlan ExampleState Nat where
  tasks := [taskX, taskY]
  ids_nodup := by simp [taskX, taskY]
  commuting := by
    constructor
    intro first firstMember second secondMember
    simp [taskX, taskY] at firstMember secondMember
    rcases firstMember with rfl | rfl <;>
      rcases secondMember with rfl | rfl <;>
      first
      | rfl
      | apply Schedule.seq_commute
        intro state
        refine { successor_eq := ?_, recovery_eq := ?_ }
        · cases state
          rfl
        · funext current
          cases current
          rfl

def exampleBefore : ExampleState := { x := 10, y := 20, z := 30 }

def exampleInitial : Runtime examplePlan := Runtime.initial examplePlan exampleBefore

def exampleIndex0 : Fin examplePlan.tasks.length := ⟨0, by decide⟩

def exampleIndex1 : Fin examplePlan.tasks.length := ⟨1, by decide⟩

theorem exampleIndex1_ne_0 : exampleIndex1 ≠ exampleIndex0 := by decide

theorem exampleIndex0_ne_1 : exampleIndex0 ≠ exampleIndex1 := by decide

def exampleAfterStart0 : Runtime examplePlan := exampleInitial.start exampleIndex0

def exampleAfterStart1 : Runtime examplePlan := exampleAfterStart0.start exampleIndex1

def exampleAfterComplete1 : Runtime examplePlan := exampleAfterStart1.complete exampleIndex1

def exampleAfterComplete0 : Runtime examplePlan := exampleAfterComplete1.complete exampleIndex0

def exampleStart0 : Step examplePlan exampleInitial (exampleInitial.start exampleIndex0) :=
  .start exampleIndex0 rfl

def exampleStart1 : Step examplePlan exampleAfterStart0 exampleAfterStart1 :=
  .start exampleIndex1 (by
    simp [exampleAfterStart0, exampleInitial, Runtime.initial, Runtime.start,
      Runtime.updatePhase, exampleIndex1_ne_0])

def exampleComplete1 : Step examplePlan exampleAfterStart1 exampleAfterComplete1 :=
  .complete exampleIndex1 (by
    simp [exampleAfterStart1, exampleAfterStart0, exampleInitial, Runtime.initial,
      Runtime.start, Runtime.updatePhase])

def exampleComplete0 : Step examplePlan exampleAfterComplete1 exampleAfterComplete0 :=
  .complete exampleIndex0 (by
    simp [exampleAfterComplete1, exampleAfterStart1, exampleAfterStart0, exampleInitial,
      Runtime.initial, Runtime.start, Runtime.complete, Runtime.updatePhase,
      exampleIndex0_ne_1])

def exampleRaceTrace : Trace examplePlan exampleInitial exampleAfterComplete0 :=
  .cons exampleStart0
    (.cons exampleStart1
      (.cons exampleComplete1
        (.cons exampleComplete0 (.nil exampleAfterComplete0))))

theorem exampleRaceTrace_successful : exampleRaceTrace.successful := by
  simp [exampleRaceTrace, exampleStart0, exampleStart1, exampleComplete1,
    exampleComplete0, Trace.successful, Step.kind]

theorem exampleRaceTrace_completionTasks :
    exampleRaceTrace.completionTasks = [taskY, taskX] := by
  rfl

theorem exampleRaceTrace_completion_ids : exampleRaceTrace.completionIds = [1, 0] := by
  rfl

theorem exampleRaceTrace_completion_permutation :
    (examplePlan.tasks.map Task.effect).Perm
      (exampleRaceTrace.completionTasks.map Task.effect) := by
  rw [exampleRaceTrace_completionTasks]
  simpa [examplePlan, taskX, taskY] using
    (List.Perm.swap (bumpX 1) (bumpY 2) ([] : List (Effect ExampleState))).symm

theorem exampleRaceTrace_index0_terminal :
    (exampleAfterComplete0.phase exampleIndex0).isTerminal = true := by
  rfl

theorem exampleRaceTrace_index1_terminal :
    (exampleAfterComplete0.phase exampleIndex1).isTerminal = true := by
  simp [exampleAfterComplete0, exampleAfterComplete1, Runtime.complete,
    Runtime.updatePhase, Phase.isTerminal, exampleIndex1_ne_0]

theorem exampleRaceTrace_final_model :
    exampleAfterComplete0.model = { x := 11, y := 22, z := 30 } := by
  rfl

def exampleCancelInitial : Runtime examplePlan := Runtime.initial examplePlan exampleBefore

def exampleCancelStep : Step examplePlan exampleCancelInitial
    (exampleCancelInitial.cancel exampleIndex1 "user") :=
  .cancel exampleIndex1 "user" (Or.inl rfl)

theorem exampleCancel_preserves_model :
    (exampleCancelInitial.cancel exampleIndex1 "user").model = exampleBefore := rfl

theorem exampleCancel_is_terminal :
    (exampleCancelInitial.cancel exampleIndex1 "user").phase exampleIndex1 =
      .cancelled "user" := by
  simp [Runtime.cancel, Runtime.updatePhase]

end Cordis.AsyncHarness
