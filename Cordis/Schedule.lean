import Cordis.Batch

/-!
# Arbitrary finite semantic schedules

This module generalizes the two-call batch theorem to arbitrary finite lists of certified
commuting pure effects. A `List.Perm` may reorder evaluation, but `runEffects` produces the same
successor and captured recovery function, and every scheduled result recovers its predecessor.

This is a semantic sequential-reordering theorem. It creates no tasks and proves no wall-clock
parallelism, fairness, cancellation, failure atomicity, result ordering, or full CORDIS
arbitrary-removal theorem.
-/

namespace Cordis.Schedule

open Cordis

universe u

/-- Execute effects from left to right and retain their composed LIFO recovery. -/
def runEffects {State : Type u} : List (Effect State) → Effect State
  | [] => Effect.identity
  | effect :: rest => Effect.seq effect (runEffects rest)

@[simp]
theorem runEffects_nil {State : Type u} : runEffects ([] : List (Effect State)) = Effect.identity :=
  rfl

@[simp]
theorem runEffects_cons
    {State : Type u} (effect : Effect State) (rest : List (Effect State)) :
    runEffects (effect :: rest) = Effect.seq effect (runEffects rest) := rfl

theorem runEffects_append
    {State : Type u}
    (first second : List (Effect State)) :
    runEffects (first ++ second) = Effect.seq (runEffects first) (runEffects second) := by
  induction first with
  | nil => exact (Effect.identity_seq (runEffects second)).symm
  | cons effect rest inductionHypothesis =>
      simp only [List.cons_append, runEffects]
      rw [inductionHypothesis]
      exact (Effect.seq_assoc effect (runEffects rest) (runEffects second)).symm

/-- A global independence certificate makes the two sequential orders exactly equal. -/
theorem seq_commute
    {State : Type u}
    {first second : Effect State}
    (independent : Effect.Independent first second) :
    Effect.seq first second = Effect.seq second first := by
  funext before
  exact (independent before).seq_applied_eq

/-- Every pair drawn from a finite effect family commutes as a complete applied effect. -/
structure CommutingFamily
    {State : Type u} (effects : List (Effect State)) : Prop where
  commute :
    ∀ {first}, first ∈ effects →
    ∀ {second}, second ∈ effects →
      Effect.seq first second = Effect.seq second first

namespace CommutingFamily

theorem tail
    {State : Type u}
    {head : Effect State}
    {effects : List (Effect State)}
    (family : CommutingFamily (head :: effects)) : CommutingFamily effects where
  commute := fun {_first} firstMember {_second} secondMember =>
    family.commute (List.mem_cons_of_mem head firstMember)
      (List.mem_cons_of_mem head secondMember)

theorem permute
    {State : Type u}
    {_first _second : List (Effect State)}
    (family : CommutingFamily _first)
    (permutation : _first.Perm _second) : CommutingFamily _second where
  commute := fun {_left} leftMember {_right} rightMember =>
    family.commute (permutation.mem_iff.mpr leftMember)
      (permutation.mem_iff.mpr rightMember)

end CommutingFamily

/-- Any permutation of one commuting finite family denotes the same composite effect. -/
theorem runEffects_eq_of_perm
    {State : Type u}
    {first second : List (Effect State)}
    (permutation : first.Perm second)
    (family : CommutingFamily first) :
    runEffects first = runEffects second := by
  induction permutation with
  | nil => rfl
  | cons head permutation inductionHypothesis =>
      exact congrArg (Effect.seq head) (inductionHypothesis family.tail)
  | swap left right rest =>
      let suffix := runEffects rest
      calc
        Effect.seq right (Effect.seq left suffix) =
            Effect.seq (Effect.seq right left) suffix :=
          (Effect.seq_assoc right left suffix).symm
        _ = Effect.seq (Effect.seq left right) suffix :=
          congrArg (fun effect => Effect.seq effect suffix)
            (family.commute (by simp) (by simp))
        _ = Effect.seq left (Effect.seq right suffix) :=
          Effect.seq_assoc left right suffix
  | trans firstPermutation secondPermutation firstHypothesis secondHypothesis =>
      exact (firstHypothesis family).trans
        (secondHypothesis (family.permute firstPermutation))

/-- A proposed finite evaluation order certified to permute one commuting canonical family. -/
structure CertifiedSchedule
    {State : Type u} (canonical : List (Effect State)) where
  scheduled : List (Effect State)
  permutation : canonical.Perm scheduled
  commuting : CommutingFamily canonical

namespace CertifiedSchedule

/-- Execute the scheduled order at an exact predecessor. -/
def execute
    {State : Type u}
    {canonical : List (Effect State)}
    (schedule : CertifiedSchedule canonical)
    (before : State) : Applied State before :=
  runEffects schedule.scheduled before

/-- The scheduled composite effect is exactly the canonical composite. -/
theorem effect_eq
    {State : Type u}
    {canonical : List (Effect State)}
    (schedule : CertifiedSchedule canonical) :
    runEffects schedule.scheduled = runEffects canonical :=
  (runEffects_eq_of_perm schedule.permutation schedule.commuting).symm

/-- Any certified order produces the canonical successor. -/
theorem after_eq
    {State : Type u}
    {canonical : List (Effect State)}
    (schedule : CertifiedSchedule canonical)
    (before : State) :
    (schedule.execute before).after = (runEffects canonical before).after := by
  exact congrArg (fun effect : Effect State => (effect before).after) schedule.effect_eq

/-- Any certified order captures exactly the canonical recovery function. -/
theorem undo_eq
    {State : Type u}
    {canonical : List (Effect State)}
    (schedule : CertifiedSchedule canonical)
    (before : State) :
    (schedule.execute before).undo = (runEffects canonical before).undo := by
  exact congrArg (fun effect : Effect State => (effect before).undo) schedule.effect_eq

/-- Any certified schedule recovers the exact predecessor supplied at execution. -/
theorem recovers
    {State : Type u}
    {canonical : List (Effect State)}
    (schedule : CertifiedSchedule canonical)
    (before : State) :
    (schedule.execute before).undo (schedule.execute before).after = before :=
  (schedule.execute before).undo_after

end CertifiedSchedule

/-! ## Three-effect example -/

structure Triple where
  x : Nat
  y : Nat
  z : Nat
deriving DecidableEq, Repr

def bumpX (amount : Nat) : Effect Triple := fun before => {
  after := { before with x := before.x + amount }
  undo := fun current => { current with x := current.x - amount }
  undo_after := by cases before; simp
}

def bumpY (amount : Nat) : Effect Triple := fun before => {
  after := { before with y := before.y + amount }
  undo := fun current => { current with y := current.y - amount }
  undo_after := by cases before; simp
}

def bumpZ (amount : Nat) : Effect Triple := fun before => {
  after := { before with z := before.z + amount }
  undo := fun current => { current with z := current.z - amount }
  undo_after := by cases before; simp
}

def exampleX : Effect Triple := bumpX 1
def exampleY : Effect Triple := bumpY 2
def exampleZ : Effect Triple := bumpZ 3

def exampleCanonical : List (Effect Triple) := [exampleX, exampleY, exampleZ]

theorem exampleCommuting : CommutingFamily exampleCanonical := by
  constructor
  intro first firstMember second secondMember
  simp only [exampleCanonical, List.mem_cons, List.not_mem_nil, or_false] at firstMember
  simp only [exampleCanonical, List.mem_cons, List.not_mem_nil, or_false] at secondMember
  rcases firstMember with rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl <;>
    first
    | rfl
    | apply seq_commute
      intro before
      refine { after_eq := ?_, undo_eq := ?_ }
      · cases before
        rfl
      · funext current
        cases current
        rfl

def reverseSchedule : CertifiedSchedule exampleCanonical where
  scheduled := [exampleZ, exampleY, exampleX]
  permutation := by
    simpa [exampleCanonical] using (List.reverse_perm exampleCanonical).symm
  commuting := exampleCommuting

def rotateSchedule : CertifiedSchedule exampleCanonical where
  scheduled := [exampleY, exampleZ, exampleX]
  permutation := by
    simpa [exampleCanonical] using
      (List.perm_append_comm :
        ([exampleX] ++ [exampleY, exampleZ]).Perm
          ([exampleY, exampleZ] ++ [exampleX]))
  commuting := exampleCommuting

def exampleBefore : Triple := { x := 10, y := 20, z := 30 }

theorem reverseSchedule_after :
    (reverseSchedule.execute exampleBefore).after = { x := 11, y := 22, z := 33 } := rfl

theorem rotateSchedule_after :
    (rotateSchedule.execute exampleBefore).after = { x := 11, y := 22, z := 33 } := rfl

theorem example_orders_equal :
    reverseSchedule.execute exampleBefore = rotateSchedule.execute exampleBefore := by
  exact congrArg (fun effect : Effect Triple => effect exampleBefore)
    (reverseSchedule.effect_eq.trans rotateSchedule.effect_eq.symm)

theorem reverseSchedule_recovers :
    (reverseSchedule.execute exampleBefore).undo
        (reverseSchedule.execute exampleBefore).after = exampleBefore :=
  reverseSchedule.recovers exampleBefore

end Cordis.Schedule
