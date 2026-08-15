import Cordis.Api

/-!
# Dependent provider registries

The registry is a dependent partial map. Updating one key retains the value
type selected by that key, and the inverse of an update needs to remember only
the overwritten binding.
-/

namespace Cordis
namespace Registry

/-- Replace the binding at one operation, preserving all other bindings. -/
def setAt
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op)
    (value : Option (Provider sig target)) : Registry sig :=
  fun op =>
    if same : op = target then
      same.symm ▸ value
    else
      registry op

@[simp]
theorem setAt_same
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op)
    (value : Option (Provider sig target)) :
    setAt registry target value target = value := by
  simp [setAt]

@[simp]
theorem setAt_other
    {sig : Signature}
    (registry : Registry sig)
    (target op : sig.Op)
    (value : Option (Provider sig target))
    (different : op ≠ target) :
    setAt registry target value op = registry op := by
  simp [setAt, different]

/-- Installing a provider is a typed specialization of `setAt`. -/
def install
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op)
    (provider : Provider sig target) : Registry sig :=
  setAt registry target (some provider)

/-- Withdrawing a provider removes only its operation's binding. -/
def withdraw
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op) : Registry sig :=
  setAt registry target none

@[simp]
theorem install_same
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op)
    (provider : Provider sig target) :
    install registry target provider target = some provider := by
  simp [install]

@[simp]
theorem withdraw_same
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op) :
    withdraw registry target target = none := by
  simp [withdraw]

/-- Restoring the overwritten binding exactly recovers the prior registry. -/
theorem setAt_restore
    {sig : Signature}
    (registry : Registry sig)
    (target : sig.Op)
    (replacement : Option (Provider sig target)) :
    setAt (setAt registry target replacement) target (registry target) = registry := by
  funext op
  by_cases same : op = target
  · subst op
    simp
  · simp [setAt, same]

/-- Updates at distinct operation keys commute exactly. -/
theorem setAt_commute
    {sig : Signature}
    (registry : Registry sig)
    (left right : sig.Op)
    (different : left ≠ right)
    (leftValue : Option (Provider sig left))
    (rightValue : Option (Provider sig right)) :
    setAt (setAt registry left leftValue) right rightValue =
      setAt (setAt registry right rightValue) left leftValue := by
  funext op
  by_cases isLeft : op = left
  · subst op
    simp [different]
  · by_cases isRight : op = right
    · subst op
      simp [setAt, isLeft]
    · simp [setAt, isLeft, isRight]

/-- A resolved view is constructive evidence that all declared needs are satisfied. -/
abbrev Satisfies
    (sig : Signature)
    (registry : Registry sig)
    (needs : Needs sig) :=
  View sig registry needs

/-- Empty capabilities are satisfied by every registry. -/
def satisfiesNone
    (sig : Signature)
    (registry : Registry sig) : Satisfies sig registry (fun _ => False) where
  resolve _ impossible := False.elim impossible

/-- A singleton capability is satisfied by an explicitly present provider. -/
def satisfiesOne
    {sig : Signature}
    {registry : Registry sig}
    (op : sig.Op)
    (provider : Provider sig op)
    (present : registry op = some provider) :
    Satisfies sig registry (fun candidate => candidate = op) where
  resolve candidate declared := by
    subst candidate
    exact { provider, present }

end Registry
end Cordis
