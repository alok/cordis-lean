import Cordis.ParallelHarness

/-!
# Proof-carrying finite Harness schedules

`ParallelHarness` certifies one parallel window followed by at most one exclusive barrier.  This
module lifts that certificate to an arbitrary finite sequence of windows and barriers.  Each window
may evaluate its pure tasks in a different certified order, while the schedule itself retains the
model-order reports and one exact composed recovery function.

The result is still a pure reference scheduler.  It does not start `IO` tasks, model wall-clock
overlap, promise races, fairness, cancellation delivery, or the TypeScript Harness scheduler.
-/

namespace Cordis.ParallelSchedule

open Cordis
open Cordis.ParallelHarness

universe u v

set_option autoImplicit false

/-- One finite schedule segment: a certified parallel window or an exclusive task. -/
inductive Segment (State : Type u) (Result : Type v) where
  | window (window : ParallelWindow State Result)
  | barrier (task : ExclusiveTask State Result)

namespace SegmentData

variable {State : Type u} {Result : Type v}

/-- Public IDs committed by one segment in model order. -/
def ids : Segment State Result -> List Nat
  | Segment.window window => window.canonical.map Task.id
  | Segment.barrier task => [task.task.id]

/-- The model-order pure effect represented by a segment. -/
def canonicalEffect : Segment State Result -> Effect State
  | Segment.window window => window.canonicalEffect
  | Segment.barrier task => task.task.effect

/-- The evaluated pure effect represented by a segment. -/
def scheduledEffect : Segment State Result -> Effect State
  | Segment.window window => window.scheduledEffect
  | Segment.barrier task => task.task.effect

theorem effect_eq (segment : Segment State Result) :
    SegmentData.scheduledEffect segment = SegmentData.canonicalEffect segment := by
  cases segment with
  | window window =>
      simpa [SegmentData.scheduledEffect, SegmentData.canonicalEffect] using window.effect_eq
  | barrier task => rfl

private def committedReport (committed : Committed Result) : Report Result :=
  { id := committed.id, status := .completed committed.value }

/-- Reports are emitted in model order inside a window and at the barrier's current state. -/
def reports (segment : Segment State Result) (before : State) : List (Report Result) :=
  match segment with
  | Segment.window window =>
      (WindowOutcome.execute window before).committed.map committedReport
  | Segment.barrier task => [Report.completed task.task before]

private theorem evaluateResults_ids
    (tasks : List (Task State Result)) (before : State) :
    (evaluateResults tasks before).map Committed.id = tasks.map Task.id := by
  induction tasks generalizing before with
  | nil => rfl
  | cons task rest inductionHypothesis =>
      simp only [evaluateResults_cons, List.map_cons]
      exact congrArg (List.cons task.id) (inductionHypothesis (task.effect before).after)

theorem reports_ids (segment : Segment State Result) (before : State) :
    (SegmentData.reports segment before).map Report.id = SegmentData.ids segment := by
  cases segment with
  | window window =>
      simp only [reports, ids]
      simp only [WindowOutcome.execute, List.map_map]
      exact evaluateResults_ids window.canonical before
  | barrier task =>
      change [task.task.id] = [task.task.id]
      rfl

end SegmentData

/-- A finite sequence of segments with one globally unique model-order call-ID ledger. -/
structure Plan (State : Type u) (Result : Type v) where
  segments : List (Segment State Result)
  ids_nodup : (segments.flatMap SegmentData.ids).Nodup

namespace Plan

variable {State : Type u} {Result : Type v}

/-- Canonical model-order effect for the complete schedule. -/
def canonicalEffect (plan : Plan State Result) : Effect State :=
  Schedule.runEffects (plan.segments.map SegmentData.canonicalEffect)

/-- Effect obtained by evaluating each window in its supplied schedule order. -/
def scheduledEffect (plan : Plan State Result) : Effect State :=
  Schedule.runEffects (plan.segments.map SegmentData.scheduledEffect)

/-- Reports emitted while walking the schedule in its evaluated state order. -/
def reportsWith
    (effect : Segment State Result -> Effect State)
    : List (Segment State Result) -> State -> List (Report Result)
  | [], _ => []
  | segment :: rest, before =>
      SegmentData.reports segment before ++
        reportsWith effect rest (effect segment before).after

def reports (plan : Plan State Result) (before : State) : List (Report Result) :=
  reportsWith SegmentData.scheduledEffect plan.segments before

def canonicalReports (plan : Plan State Result) (before : State) : List (Report Result) :=
  reportsWith SegmentData.canonicalEffect plan.segments before

theorem segment_effects_eq (plan : Plan State Result) :
    plan.segments.map SegmentData.scheduledEffect =
      plan.segments.map SegmentData.canonicalEffect := by
  induction plan.segments with
  | nil => rfl
  | cons segment rest inductionHypothesis =>
      simp only [List.map_cons]
      rw [Cordis.ParallelSchedule.SegmentData.effect_eq segment, inductionHypothesis]

theorem effect_eq (plan : Plan State Result) :
    plan.scheduledEffect = plan.canonicalEffect := by
  exact congrArg Schedule.runEffects plan.segment_effects_eq

theorem reportsWith_eq_canonical
    (segments : List (Segment State Result)) (before : State) :
    reportsWith SegmentData.scheduledEffect segments before =
      reportsWith SegmentData.canonicalEffect segments before := by
  induction segments generalizing before with
  | nil => rfl
  | cons segment rest inductionHypothesis =>
      simp only [reportsWith]
      rw [Cordis.ParallelSchedule.SegmentData.effect_eq segment]
      congr 1
      exact inductionHypothesis _

theorem reports_eq_canonical (plan : Plan State Result) (before : State) :
    plan.reports before = plan.canonicalReports before := by
  exact reportsWith_eq_canonical plan.segments before

theorem reports_ids (plan : Plan State Result) (before : State) :
    (plan.reports before).map Report.id = plan.segments.flatMap SegmentData.ids := by
  have aux : ∀ (segments : List (Segment State Result)) (before : State),
      (reportsWith SegmentData.scheduledEffect segments before).map Report.id =
        segments.flatMap SegmentData.ids := by
    intro segments
    induction segments with
    | nil => intro _; rfl
    | cons segment rest inductionHypothesis =>
        intro before
        simp only [reportsWith, List.map_append, List.map_cons, List.flatMap]
        rw [Cordis.ParallelSchedule.SegmentData.reports_ids segment before]
        rw [inductionHypothesis (SegmentData.scheduledEffect segment before).after]
        simp [List.flatMap]
  exact aux plan.segments before

theorem reports_ids_nodup (plan : Plan State Result) (before : State) :
    (plan.reports before).map Report.id |>.Nodup := by
  rw [plan.reports_ids before]
  exact plan.ids_nodup

/-- The proof-carrying result of evaluating an arbitrary finite schedule. -/
structure Outcome (plan : Plan State Result) (before : State) where
  applied : Applied State before
  reports : List (Report Result)
  applied_eq_scheduled : applied = plan.scheduledEffect before
  reports_eq : reports = plan.reports before

def execute (plan : Plan State Result) (before : State) : Outcome plan before :=
  { applied := plan.scheduledEffect before
    reports := plan.reports before
    applied_eq_scheduled := rfl
    reports_eq := rfl }

theorem execute_after_eq_canonical (plan : Plan State Result) (before : State) :
    (plan.execute before).applied.after = (plan.canonicalEffect before).after := by
  rw [(plan.execute before).applied_eq_scheduled]
  exact congrArg (fun effect : Effect State => (effect before).after) plan.effect_eq

theorem execute_undo_eq_canonical
    (plan : Plan State Result) (before current : State) :
    (plan.execute before).applied.undo current =
      (plan.canonicalEffect before).undo current := by
  rw [(plan.execute before).applied_eq_scheduled]
  exact congrArg (fun effect : Effect State => (effect before).undo current) plan.effect_eq

theorem execute_recovers (plan : Plan State Result) (before : State) :
    (plan.execute before).applied.undo (plan.execute before).applied.after = before :=
  (plan.execute before).applied.undo_after

theorem execute_reports_ids (plan : Plan State Result) (before : State) :
    (plan.execute before).reports.map Report.id = plan.segments.flatMap SegmentData.ids := by
  rw [(plan.execute before).reports_eq]
  exact plan.reports_ids before

theorem execute_reports_ids_nodup (plan : Plan State Result) (before : State) :
    (plan.execute before).reports.map Report.id |>.Nodup := by
  rw [(plan.execute before).reports_eq]
  exact plan.reports_ids_nodup before

theorem execute_reports_model_order (plan : Plan State Result) (before : State) :
    (plan.execute before).reports = plan.canonicalReports before := by
  rw [(plan.execute before).reports_eq]
  exact plan.reports_eq_canonical before

end Plan

/-! ## A three-segment executable witness -/

def splitWindowXY : ParallelWindow ExampleState Nat where
  canonical := [taskX, taskY]
  scheduled := [taskY, taskX]
  canonical_ids_nodup := by simp [taskX, taskY]
  canonical_parallel := by
    intro task membership
    simp [taskX, taskY] at membership ⊢
    rcases membership with rfl | rfl <;> rfl
  scheduled_parallel := by
    intro task membership
    simp [taskX, taskY] at membership ⊢
    rcases membership with rfl | rfl <;> rfl
  ids_permutation := by
    simpa [taskX, taskY] using
      (List.reverse_perm ([0, 1] : List Nat)).symm
  effect_permutation := by
    simpa [taskX, taskY] using
      (List.reverse_perm ([bumpX 1, bumpY 2] : List (Effect ExampleState))).symm
  commuting := by
    constructor
    intro first firstMembership second secondMembership
    simp [taskX, taskY] at firstMembership secondMembership
    rcases firstMembership with rfl | rfl <;>
      rcases secondMembership with rfl | rfl <;>
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
    simp [evaluateResults, evaluateWithState, Task.result, Task.effect, taskX, taskY,
      bumpX, bumpY]
    exact (List.reverse_perm
      ([{ id := 0, value := 10 }, { id := 1, value := 20 }] : List (Committed Nat)))

def splitWindowZ : ParallelWindow ExampleState Nat where
  canonical := [taskZ]
  scheduled := [taskZ]
  canonical_ids_nodup := by simp [taskZ]
  canonical_parallel := by
    intro task membership
    simp [taskZ] at membership ⊢
    rcases membership with rfl
    rfl
  scheduled_parallel := by
    intro task membership
    simp [taskZ] at membership ⊢
    rcases membership with rfl
    rfl
  ids_permutation := by rfl
  effect_permutation := by rfl
  commuting := by
    constructor
    intro first firstMembership second secondMembership
    simp at firstMembership secondMembership
    rcases firstMembership with rfl
    rcases secondMembership with rfl
    rfl
  result_permutation := by
    intro state
    exact List.Perm.refl _

def examplePlan : Plan ExampleState Nat where
  segments := [.window splitWindowXY, .window splitWindowZ, .barrier barrierTask]
  ids_nodup := by
    simp [SegmentData.ids, splitWindowXY, splitWindowZ, barrierTask, taskX, taskY, taskZ]

def exampleBefore : ExampleState := { x := 10, y := 20, z := 30 }

theorem example_after :
    (examplePlan.execute exampleBefore).applied.after = { x := 11, y := 22, z := 33 } := by
  rfl

theorem example_reports :
    (examplePlan.execute exampleBefore).reports =
      [{ id := 0, status := .completed 10 },
       { id := 1, status := .completed 20 },
       { id := 2, status := .completed 30 },
       { id := 3, status := .completed 66 }] := by
  rfl

theorem example_report_ids :
    (examplePlan.execute exampleBefore).reports.map Report.id = [0, 1, 2, 3] := by
  rfl

theorem example_recovers :
    (examplePlan.execute exampleBefore).applied.undo
      (examplePlan.execute exampleBefore).applied.after = exampleBefore :=
  examplePlan.execute_recovers exampleBefore

end Cordis.ParallelSchedule
