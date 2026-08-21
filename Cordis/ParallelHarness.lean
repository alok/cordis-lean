import Cordis.Schedule

/-!
# Proof-carrying finite Harness scheduling

This module closes one explicitly bounded Harness-facing gap.  A `ParallelWindow` carries a
canonical model order, an arbitrary evaluated order, complete-effect commutation, and a result
multiset certificate.  `execute` evaluates the scheduled effects but exposes results in the
canonical order.  `Plan` may then run one explicitly exclusive barrier after the window.

Cancellation is represented by a pure drain: every still-pending task receives a synthetic abort
report and no model effect is applied.  The module proves endpoint, recovery, ordering, barrier,
and drain facts.  It does not start `IO` tasks, claim wall-clock parallelism, or refine the
TypeScript scheduler; those remain external adapter obligations.
-/

namespace Cordis.ParallelHarness

open Cordis

universe u v

set_option autoImplicit false

/-- Whether a call may share a parallel window or must be isolated as a barrier. -/
inductive DispatchClass where
  | parallel
  | exclusive
deriving DecidableEq, Repr

/-- A pure proof-carrying task with a stable public identifier. -/
structure Task (State : Type u) (Result : Type v) where
  id : Nat
  mode : DispatchClass
  call : PureCall State Result

namespace Task

variable {State : Type u} {Result : Type v}

abbrev effect (task : Task State Result) : Effect State := task.call.effect

abbrev result (task : Task State Result) : State → Result := task.call.result

theorem effect_eq (task : Task State Result) : task.effect = task.call.effect := rfl

theorem result_eq (task : Task State Result) : task.result = task.call.result := rfl

end Task

/-- A result retained by the model-order commit log. -/
structure Committed (Result : Type v) where
  id : Nat
  value : Result

/-- A terminal report, including synthetic cancellation without a model transition. -/
inductive ReportStatus (Result : Type v) where
  | completed (value : Result)
  | cancelled (reason : String)

structure Report (Result : Type v) where
  id : Nat
  status : ReportStatus Result

namespace Report

variable {State : Type u} {Result : Type v}

def completed (task : Task State Result) (state : State) : Report Result :=
  { id := task.id, status := .completed (task.result state) }

def cancelled (task : Task State Result) (reason : String) : Report Result :=
  { id := task.id, status := .cancelled reason }

theorem cancelled_id (task : Task State Result) (reason : String) :
    (cancelled task reason).id = task.id := rfl

theorem cancelled_status (task : Task State Result) (reason : String) :
    (cancelled task reason).status = .cancelled reason := rfl

end Report

/-- Tasks accepted into the barrier slot are intrinsically exclusive. -/
structure ExclusiveTask (State : Type u) (Result : Type v) where
  task : Task State Result
  mode_eq : task.mode = .exclusive

namespace ExclusiveTask

variable {State : Type u} {Result : Type v}

theorem mode_is_exclusive (task : ExclusiveTask State Result) : task.task.mode = .exclusive :=
  task.mode_eq

end ExclusiveTask

/-- Sequentially evaluate tasks while retaining each task's observed result. -/
def evaluateWithState
    {State : Type u} {Result : Type v} :
    List (Task State Result) → State → State × List (Committed Result)
  | [], state => (state, [])
  | task :: rest, state =>
      let applied := task.effect state
      let tail := evaluateWithState rest applied.after
      (tail.1, { id := task.id, value := task.result state } :: tail.2)

def evaluateState
    {State : Type u} {Result : Type v} (tasks : List (Task State Result)) (state : State) : State :=
  (evaluateWithState tasks state).1

def evaluateResults
    {State : Type u} {Result : Type v} (tasks : List (Task State Result)) (state : State) :
    List (Committed Result) :=
  (evaluateWithState tasks state).2

@[simp]
theorem evaluateWithState_nil
    {State : Type u} {Result : Type v} (state : State) :
    evaluateWithState ([] : List (Task State Result)) state = (state, []) := rfl

@[simp]
theorem evaluateWithState_cons
    {State : Type u} {Result : Type v}
    (task : Task State Result) (rest : List (Task State Result)) (state : State) :
    evaluateWithState (task :: rest) state =
      let applied := task.effect state
      let tail := evaluateWithState rest applied.after
      (tail.1, { id := task.id, value := task.result state } :: tail.2) := rfl

@[simp]
theorem evaluateState_eq_runEffects
    {State : Type u} {Result : Type v}
    (tasks : List (Task State Result)) (state : State) :
    evaluateState tasks state = (Schedule.runEffects (tasks.map Task.effect) state).after := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task rest ih =>
      simp only [evaluateState, evaluateWithState_cons, Schedule.runEffects, List.map_cons,
        Effect.seq_after]
      exact ih (task.effect state).after

@[simp]
theorem evaluateResults_cons
    {State : Type u} {Result : Type v}
    (task : Task State Result) (rest : List (Task State Result)) (state : State) :
    evaluateResults (task :: rest) state =
      { id := task.id, value := task.result state } ::
        evaluateResults rest (task.effect state).after := by
  rfl

theorem evaluateResults_length
    {State : Type u} {Result : Type v}
    (tasks : List (Task State Result)) (state : State) :
    (evaluateResults tasks state).length = tasks.length := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task rest ih =>
      simp only [evaluateResults_cons, List.length_cons]
      rw [ih]

/-- A finite parallel window and its proof obligations. -/
structure ParallelWindow (State : Type u) (Result : Type v) where
  canonical : List (Task State Result)
  scheduled : List (Task State Result)
  canonical_ids_nodup : (canonical.map Task.id).Nodup
  canonical_parallel : ∀ task, task ∈ canonical → task.mode = .parallel
  scheduled_parallel : ∀ task, task ∈ scheduled → task.mode = .parallel
  ids_permutation : (canonical.map Task.id).Perm (scheduled.map Task.id)
  effect_permutation :
    (canonical.map Task.effect).Perm (scheduled.map Task.effect)
  commuting : Schedule.CommutingFamily (canonical.map Task.effect)
  /-- Evaluating in the scheduled order yields the same result multiset as model order. -/
  result_permutation : ∀ state,
    (evaluateResults scheduled state).Perm (evaluateResults canonical state)

namespace ParallelWindow

variable {State : Type u} {Result : Type v}

def canonicalEffect (window : ParallelWindow State Result) : Effect State :=
  Schedule.runEffects (window.canonical.map Task.effect)

def scheduledEffect (window : ParallelWindow State Result) : Effect State :=
  Schedule.runEffects (window.scheduled.map Task.effect)

theorem effect_eq (window : ParallelWindow State Result) :
    window.scheduledEffect = window.canonicalEffect := by
  exact Schedule.runEffects_eq_of_perm window.effect_permutation window.commuting |>.symm

theorem scheduled_after_eq_canonical
    (window : ParallelWindow State Result) (state : State) :
    (window.scheduledEffect state).after = (window.canonicalEffect state).after := by
  exact congrArg (fun effect : Effect State => (effect state).after) window.effect_eq

theorem scheduled_undo_eq_canonical
    (window : ParallelWindow State Result) (state current : State) :
    (window.scheduledEffect state).undo current =
      (window.canonicalEffect state).undo current := by
  exact congrArg (fun effect : Effect State => (effect state).undo current) window.effect_eq

theorem result_length_eq_canonical
    (window : ParallelWindow State Result) (state : State) :
    (evaluateResults window.scheduled state).length = window.canonical.length := by
  calc
    (evaluateResults window.scheduled state).length = window.scheduled.length :=
      evaluateResults_length window.scheduled state
    _ = window.canonical.length := by
      simpa only [List.length_map] using window.ids_permutation.length_eq.symm

end ParallelWindow

/-- The proof-carrying result of evaluating one parallel window. -/
structure WindowOutcome
    (State : Type u) (Result : Type v)
    (window : ParallelWindow State Result) (before : State) where
  applied : Applied State before
  evaluated : List (Committed Result)
  committed : List (Committed Result)
  applied_eq_scheduled : applied = window.scheduledEffect before
  evaluated_eq_scheduled : evaluated = evaluateResults window.scheduled before
  committed_eq_canonical : committed = evaluateResults window.canonical before
  committed_perm_evaluated : evaluated.Perm committed

namespace WindowOutcome

variable {State : Type u} {Result : Type v}

def execute
    (window : ParallelWindow State Result) (before : State) :
    WindowOutcome State Result window before :=
  { applied := window.scheduledEffect before
    evaluated := evaluateResults window.scheduled before
    committed := evaluateResults window.canonical before
    applied_eq_scheduled := rfl
    evaluated_eq_scheduled := rfl
    committed_eq_canonical := rfl
    committed_perm_evaluated := window.result_permutation before }

@[simp]
theorem execute_applied
    (window : ParallelWindow State Result) (before : State) :
    (execute window before).applied = window.scheduledEffect before := rfl

theorem execute_after_eq_canonical
    (window : ParallelWindow State Result) (before : State) :
    (execute window before).applied.after = (window.canonicalEffect before).after := by
  rw [execute_applied, window.scheduled_after_eq_canonical]

theorem execute_undo_eq_canonical
    (window : ParallelWindow State Result) (before current : State) :
    (execute window before).applied.undo current =
      (window.canonicalEffect before).undo current := by
  rw [execute_applied]
  exact window.scheduled_undo_eq_canonical before current

theorem execute_recovers
    (window : ParallelWindow State Result) (before : State) :
    (execute window before).applied.undo (execute window before).applied.after = before :=
  (execute window before).applied.undo_after

theorem committed_is_model_order
    (window : ParallelWindow State Result) (before : State) :
    (execute window before).committed = evaluateResults window.canonical before := rfl

theorem commit_length_eq
    (window : ParallelWindow State Result) (before : State) :
    (execute window before).committed.length = window.canonical.length := by
  rw [committed_is_model_order, evaluateResults_length]

end WindowOutcome

/-- A plan's optional barrier is isolated from the parallel window by its type. -/
structure Plan (State : Type u) (Result : Type v) where
  window : ParallelWindow State Result
  barrier : Option (ExclusiveTask State Result)

namespace Plan

variable {State : Type u} {Result : Type v}

def canonicalEffect (plan : Plan State Result) : Effect State :=
  match plan.barrier with
  | none => plan.window.canonicalEffect
  | some barrier => Effect.seq plan.window.canonicalEffect barrier.task.effect

def scheduledEffect (plan : Plan State Result) : Effect State :=
  match plan.barrier with
  | none => plan.window.scheduledEffect
  | some barrier => Effect.seq plan.window.scheduledEffect barrier.task.effect

theorem effect_eq (plan : Plan State Result) :
    plan.scheduledEffect = plan.canonicalEffect := by
  cases barrier : plan.barrier with
  | none =>
      simp [scheduledEffect, canonicalEffect, barrier, plan.window.effect_eq]
  | some barrierTask =>
      simp [scheduledEffect, canonicalEffect, barrier, plan.window.effect_eq]

theorem scheduled_after_eq_canonical
    (plan : Plan State Result) (state : State) :
    (plan.scheduledEffect state).after = (plan.canonicalEffect state).after := by
  exact congrArg (fun effect : Effect State => (effect state).after) plan.effect_eq

theorem scheduled_undo_eq_canonical
    (plan : Plan State Result) (state current : State) :
    (plan.scheduledEffect state).undo current = (plan.canonicalEffect state).undo current := by
  exact congrArg (fun effect : Effect State => (effect state).undo current) plan.effect_eq

structure Outcome (plan : Plan State Result) (before : State) where
  applied : Applied State before
  window : WindowOutcome State Result plan.window before
  barrierReport : Option (Report Result)
  applied_eq_scheduled : applied = plan.scheduledEffect before

def execute
    (plan : Plan State Result) (before : State) : Outcome plan before := by
  let window := WindowOutcome.execute plan.window before
  cases barrier : plan.barrier with
  | none =>
      exact {
        applied := window.applied
        window := window
        barrierReport := none
        applied_eq_scheduled := by
          simpa [scheduledEffect, barrier] using window.applied_eq_scheduled
      }
  | some barrierTask =>
      let applied := Effect.seq plan.window.scheduledEffect barrierTask.task.effect before
      exact {
        applied := applied
        window := window
        barrierReport := some (Report.completed barrierTask.task window.applied.after)
        applied_eq_scheduled := by
          simp [scheduledEffect, barrier, applied]
      }

theorem execute_after_eq_canonical
    (plan : Plan State Result) (before : State) :
    (execute plan before).applied.after = (plan.canonicalEffect before).after := by
  rw [(execute plan before).applied_eq_scheduled, plan.scheduled_after_eq_canonical]

theorem execute_recovers
    (plan : Plan State Result) (before : State) :
    (execute plan before).applied.undo (execute plan before).applied.after = before :=
  (execute plan before).applied.undo_after

theorem barrier_is_exclusive
    (plan : Plan State Result) :
    ∀ {barrierTask : ExclusiveTask State Result},
      plan.barrier = some barrierTask → barrierTask.task.mode = .exclusive := by
  intro barrierTask _
  exact barrierTask.mode_eq

theorem barrier_report_is_model_ordered
    (plan : Plan State Result) (before : State)
    {barrierTask : ExclusiveTask State Result}
    (barrier : plan.barrier = some barrierTask) :
    (execute plan before).barrierReport =
      some (Report.completed barrierTask.task
        (plan.window.scheduledEffect before).after) := by
  cases plan with
  | mk window barrierOption =>
      cases barrierOption with
      | none => simp at barrier
      | some barrierValue =>
          simp only at barrier
          cases barrier
          rfl

end Plan

/-- Why a cancellation drain was requested. -/
inductive CancelReason where
  | user
  | timeout
  | peerFailure
deriving DecidableEq, Repr

def reasonText : CancelReason → String
  | .user => "cancelled:user"
  | .timeout => "cancelled:timeout"
  | .peerFailure => "cancelled:peer-failure"

/-- Emit one synthetic abort report per still-pending task, without touching model state. -/
def drain
    {State : Type u} {Result : Type v}
    (pending : List (Task State Result)) (reason : CancelReason) : List (Report Result) :=
  pending.map fun task => Report.cancelled task (reasonText reason)

namespace drain

variable {State : Type u} {Result : Type v}

theorem length_eq
    (pending : List (Task State Result)) (reason : CancelReason) :
    (drain pending reason).length = pending.length := by
  simp [drain]

theorem ids_eq
    (pending : List (Task State Result)) (reason : CancelReason) :
    (drain pending reason).map Report.id = pending.map Task.id := by
  simp [drain, reasonText, Report.cancelled]

theorem all_cancelled
    (pending : List (Task State Result)) (reason : CancelReason) :
    ∀ report ∈ drain pending reason,
      ∃ task ∈ pending, report = Report.cancelled task (reasonText reason) := by
  intro report membership
  rcases (List.mem_map.mp (show report ∈
    pending.map (fun task => Report.cancelled task (reasonText reason)) from by
      simpa [drain] using membership)) with ⟨task, taskMembership, reportEq⟩
  exact ⟨task, taskMembership, reportEq.symm⟩

theorem no_model_effect
    (_pending : List (Task State Result)) (_reason : CancelReason) (state : State) :
    state = state := rfl

/-- A proof-carrying cancellation drain with an unchanged model endpoint. -/
structure DrainOutcome
    (State : Type u) (Result : Type v)
    (pending : List (Task State Result)) (before : State) where
  after : State
  reports : List (Report Result)
  after_eq : after = before
  reports_eq : reports = drain pending .user

def drainOutcome
    {State : Type u} {Result : Type v}
    (pending : List (Task State Result)) (before : State) :
    DrainOutcome State Result pending before :=
  { after := before
    reports := drain pending .user
    after_eq := rfl
    reports_eq := rfl }

theorem drainOutcome_after_eq
    {State : Type u} {Result : Type v}
    (pending : List (Task State Result)) (before : State) :
    (drainOutcome pending before).after = before := rfl

theorem drainOutcome_reports_ids
    {State : Type u} {Result : Type v}
    (pending : List (Task State Result)) (before : State) :
    (drainOutcome pending before).reports.map Report.id = pending.map Task.id := by
  rw [drainOutcome]
  exact drain.ids_eq pending .user

theorem drainOutcome_reports_cancelled
    {State : Type u} {Result : Type v}
    (pending : List (Task State Result)) (before : State) :
    ∀ report ∈ (drainOutcome pending before).reports,
      ∃ task ∈ pending, report = Report.cancelled task (reasonText .user) := by
  rw [drainOutcome]
  exact drain.all_cancelled pending .user

end drain

/-! ## Concrete executable finite scheduler example -/

structure ExampleState where
  x : Nat
  y : Nat
  z : Nat
deriving DecidableEq, Repr

def bumpX (amount : Nat) : Effect ExampleState := fun before => {
  after := { before with x := before.x + amount }
  undo := fun current => { current with x := current.x - amount }
  undo_after := by cases before; simp
}

def bumpY (amount : Nat) : Effect ExampleState := fun before => {
  after := { before with y := before.y + amount }
  undo := fun current => { current with y := current.y - amount }
  undo_after := by cases before; simp
}

def bumpZ (amount : Nat) : Effect ExampleState := fun before => {
  after := { before with z := before.z + amount }
  undo := fun current => { current with z := current.z - amount }
  undo_after := by cases before; simp
}

def taskX : Task ExampleState Nat :=
  { id := 0, mode := .parallel, call := { effect := bumpX 1, result := fun _ => 10 } }

def taskY : Task ExampleState Nat :=
  { id := 1, mode := .parallel, call := { effect := bumpY 2, result := fun _ => 20 } }

def taskZ : Task ExampleState Nat :=
  { id := 2, mode := .parallel, call := { effect := bumpZ 3, result := fun _ => 30 } }

def barrierTask : ExclusiveTask ExampleState Nat :=
  { task :=
      { id := 3, mode := .exclusive
        call := { effect := Effect.identity, result := fun state => state.x + state.y + state.z } }
    mode_eq := rfl }

def exampleWindow : ParallelWindow ExampleState Nat where
  canonical := [taskX, taskY, taskZ]
  scheduled := [taskZ, taskY, taskX]
  canonical_ids_nodup := by simp [taskX, taskY, taskZ]
  canonical_parallel := by
    intro task membership
    simp [taskX, taskY, taskZ] at membership ⊢
    rcases membership with rfl | rfl | rfl <;> rfl
  scheduled_parallel := by
    intro task membership
    simp [taskX, taskY, taskZ] at membership ⊢
    rcases membership with rfl | rfl | rfl <;> rfl
  ids_permutation := by
    simpa [taskX, taskY, taskZ] using
      (List.reverse_perm ([0, 1, 2] : List Nat)).symm
  effect_permutation := by
    simpa [taskX, taskY, taskZ] using
      (List.reverse_perm ([bumpX 1, bumpY 2, bumpZ 3] : List (Effect ExampleState))).symm
  commuting := by
    constructor
    intro first firstMembership second secondMembership
    simp [taskX, taskY, taskZ] at firstMembership secondMembership
    rcases firstMembership with rfl | rfl | rfl <;>
      rcases secondMembership with rfl | rfl | rfl <;>
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
  result_permutation := by
    intro state
    cases state
    simp [evaluateResults, evaluateWithState, Task.result, Task.effect, taskX, taskY, taskZ,
      bumpX, bumpY, bumpZ]
    exact (List.reverse_perm
      ([{ id := 0, value := 10 }, { id := 1, value := 20 },
        { id := 2, value := 30 }] : List (Committed Nat)))

def examplePlan : Plan ExampleState Nat :=
  { window := exampleWindow, barrier := some barrierTask }

def exampleBefore : ExampleState := { x := 10, y := 20, z := 30 }

theorem example_window_after :
    (WindowOutcome.execute exampleWindow exampleBefore).applied.after =
      { x := 11, y := 22, z := 33 } := by
  rfl

theorem example_window_committed :
    (WindowOutcome.execute exampleWindow exampleBefore).committed =
      [{ id := 0, value := 10 }, { id := 1, value := 20 }, { id := 2, value := 30 }] := by
  rfl

theorem example_plan_after :
    (Plan.execute examplePlan exampleBefore).applied.after =
      { x := 11, y := 22, z := 33 } := by
  rfl

theorem example_plan_recovers :
    (Plan.execute examplePlan exampleBefore).applied.undo
      (Plan.execute examplePlan exampleBefore).applied.after = exampleBefore :=
  Plan.execute_recovers examplePlan exampleBefore

theorem example_barrier_is_exclusive :
    examplePlan.barrier = some barrierTask → barrierTask.task.mode = .exclusive :=
  Plan.barrier_is_exclusive examplePlan

def exampleDrain : List (Report Nat) :=
  drain [taskX, taskY] .timeout

theorem exampleDrain_ids : exampleDrain.map Report.id = [0, 1] := by
  rfl

theorem exampleDrain_length : exampleDrain.length = 2 := by
  rfl

end Cordis.ParallelHarness
