import Cordis.Effect

/-!
# Proof-carrying component lifecycle

This is the finite synchronous lifecycle kernel corresponding to CORDIS's
`Inactive -> Reloading -> Active -> Unloading` machine. A committed dependency
view is retained throughout an activation episode. Leaving hides a provider;
the final unload transition additionally requires a withdrawal guard proving
that no installed consumer still resolves to that provider.
-/

namespace Cordis.Lifecycle

universe u v w

/-- Terminal status retained while a fiber is inactive. -/
inductive Outcome where
  | stopped
  | failed (message : String)
deriving BEq, DecidableEq, Repr

/-- Provider identities committed by one consumer activation. -/
structure CommittedView (Key : Type u) (Fiber : Type v) where
  resolve : Key -> Option Fiber

namespace CommittedView

/-- A committed view relies on a provider when any key resolves to it. -/
def ReliesOn
    {Key : Type u}
    {Fiber : Type v}
    (view : CommittedView Key Fiber)
    (provider : Fiber) : Prop :=
  exists key, view.resolve key = some provider

end CommittedView

/-- The dependency snapshot of a potentially installed consumer. -/
structure Consumer (Key : Type u) (Fiber : Type v) where
  fiber : Fiber
  installed : Bool
  view : CommittedView Key Fiber

/-- No installed consumer in the registry still resolves to `provider`. -/
def Withdrawable
    {Key : Type u}
    {Fiber : Type v}
    (consumers : List (Consumer Key Fiber))
    (provider : Fiber) : Prop :=
  forall consumer,
    consumer ∈ consumers ->
    consumer.installed = true ->
    Not (consumer.view.ReliesOn provider)

theorem withdrawable_empty
    {Key : Type u}
    {Fiber : Type v}
    (provider : Fiber) :
    Withdrawable (Key := Key) [] provider := by
  intro consumer member
  cases member

theorem not_withdrawable_of_relied
    {Key : Type u}
    {Fiber : Type v}
    {consumers : List (Consumer Key Fiber)}
    {provider : Fiber}
    (consumer : Consumer Key Fiber)
    (member : consumer ∈ consumers)
    (installed : consumer.installed = true)
    (relies : consumer.view.ReliesOn provider) :
    Not (Withdrawable consumers provider) := by
  intro guard
  exact guard consumer member installed relies

/-- Lifecycle states retain the modeled state and a typed LIFO activation stack. -/
inductive State (Model : Type w) (View Iterator : Type u) where
  | inactive (current : Model) (outcome : Outcome)
  | reloading
      (origin current : Model)
      (undo : UndoStack Model origin current)
      (iterator : Iterator)
      (committed : View)
  | active
      (origin current : Model)
      (undo : UndoStack Model origin current)
      (committed : View)
  | unloading
      (origin current : Model)
      (undo : UndoStack Model origin current)
      (committed : View)
      (outcome : Outcome)

/--
Legal lifecycle transitions. The provider and consumer snapshot index the
transition so `unload` cannot be constructed without its withdrawal proof.
-/
inductive Transition
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    (provider : Fiber)
    (consumers : List (Consumer Key Fiber)) :
    State Model View Iterator -> State Model View Iterator -> Type (max u v w) where
  | begin
      (outcome : Outcome)
      (origin : Model)
      (iterator : Iterator)
      (committed : View) :
      Transition provider consumers
        (.inactive origin outcome)
        (.reloading origin origin (.nil origin) iterator committed)
  | iterate
      {origin current : Model}
      {undo : UndoStack Model origin current}
      {iterator : Iterator}
      {committed : View}
      (effect : Effect Model)
      (next : Iterator) :
      Transition provider consumers
        (.reloading origin current undo iterator committed)
        (.reloading origin (effect current).after
          (.push undo (effect current)) next committed)
  | finish
      {origin current : Model}
      {undo : UndoStack Model origin current}
      {iterator : Iterator}
      {committed : View} :
      Transition provider consumers
        (.reloading origin current undo iterator committed)
        (.active origin current undo committed)
  | divert
      {origin current : Model}
      {undo : UndoStack Model origin current}
      {iterator : Iterator}
      {committed : View}
      (outcome : Outcome) :
      Transition provider consumers
        (.reloading origin current undo iterator committed)
        (.unloading origin current undo committed outcome)
  | leave
      {origin current : Model}
      {undo : UndoStack Model origin current}
      {committed : View}
      (outcome : Outcome) :
      Transition provider consumers
        (.active origin current undo committed)
        (.unloading origin current undo committed outcome)
  | unload
      {origin current : Model}
      {undo : UndoStack Model origin current}
      {committed : View}
      {outcome : Outcome}
      (guard : Withdrawable consumers provider) :
      Transition provider consumers
        (.unloading origin current undo committed outcome)
        (.inactive origin outcome)

namespace Transition

/-- The unload rule's LIFO accumulator exactly recovers activation's origin. -/
theorem unload_recovers
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    {provider : Fiber}
    {consumers : List (Consumer Key Fiber)}
    {origin current : Model}
    {undo : UndoStack Model origin current}
    {committed : View}
    {outcome : Outcome}
    (transition : Transition (View := View) (Iterator := Iterator) provider consumers
      (.unloading origin current undo committed outcome : State Model View Iterator)
      (.inactive origin outcome : State Model View Iterator)) :
    undo.recover current = origin := by
  cases transition
  exact undo.recover_after

/-- An unload transition cannot coexist with evidence of an installed dependent. -/
theorem unload_rejects_relied
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    {provider : Fiber}
    {consumers : List (Consumer Key Fiber)}
    {origin current : Model}
    {undo : UndoStack Model origin current}
    {committed : View}
    {outcome : Outcome}
    (transition : Transition (View := View) (Iterator := Iterator) provider consumers
      (.unloading origin current undo committed outcome : State Model View Iterator)
      (.inactive origin outcome : State Model View Iterator))
    (consumer : Consumer Key Fiber)
    (member : consumer ∈ consumers)
    (installed : consumer.installed = true)
    (relies : consumer.view.ReliesOn provider) : False := by
  cases transition with
  | unload guard => exact guard consumer member installed relies

/-- Leaving an active episode retains precisely the committed dependency view. -/
theorem active_successor_keeps_view
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    {provider : Fiber}
    {consumers : List (Consumer Key Fiber)}
    {origin current : Model}
    {undo : UndoStack Model origin current}
    {committed : View}
    {next : State Model View Iterator}
    (transition : Transition provider consumers
      (.active origin current undo committed) next) :
    exists outcome, next = .unloading origin current undo committed outcome := by
  cases transition with
  | leave outcome => exact ⟨outcome, rfl⟩

end Transition

/-- A composable, intrinsically typed lifecycle execution. -/
inductive Trace
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    (provider : Fiber)
    (consumers : List (Consumer Key Fiber)) :
    State Model View Iterator -> State Model View Iterator -> Type (max u v w) where
  | nil (state) : Trace provider consumers state state
  | cons
      {start middle finish}
      (step : Transition provider consumers start middle)
      (rest : Trace provider consumers middle finish) :
      Trace provider consumers start finish

namespace Trace

/-- Concatenate two lifecycle traces whose boundary states match. -/
def append
    {Key : Type u}
    {Fiber : Type v}
    {Model : Type w}
    {View Iterator : Type u}
    {provider : Fiber}
    {consumers : List (Consumer Key Fiber)}
    {start middle finish : State Model View Iterator}
    (first : Trace provider consumers start middle)
    (second : Trace provider consumers middle finish) :
    Trace provider consumers start finish :=
  match first with
  | .nil _ => second
  | .cons step rest => .cons step (append rest second)

end Trace

end Cordis.Lifecycle
