import Cordis.ContextualEquivalence
import Std

/-!
# Operational indistinguishability from finite tests

This module gives a source-honest executable model of Definition 34 and the generator-level
content of Lemma 35 from the CORDIS paper at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

A `Letter` is either an operation's forward map at a typed argument or a concrete inverse
yielded by that operation at a particular enabled seed. A `Test` is a finite list of such
letters. `observe` is executable: forward letters can fail their decidable precondition and
append a heterogeneously typed outcome, while inverse letters are total transformations and
produce no outcome. `Indistinguishable` quantifies over these finite tests; it is not defined in
terms of an assumed equivalence or admissibility predicate.

There is a precise boundary in the paper statement. Fixed-generator tests prove that every
individual yielded inverse preserves indistinguishability. The `CoeffectAt.undo_respects` API,
following Definition 24's stronger reading, compares two potentially different inverses yielded
at two related seeds. Same-test observation does not imply that paired-inverse property. The
module therefore proves Lemma 35 exactly for `GeneratorAdmissible`, and makes reconstruction
of a full `CoeffectAt` over operational indistinguishability conditional on the separate
`PairedInverseCoherent` obligation. No circular definition hides that obligation.

The module does not claim Definitions 36--42, transformation-monoid commutation, quotient
independence, or that the paper's paired-inverse sentence follows from Definition 34 alone.
-/

namespace Cordis.OperationalEquivalence

universe u v

variable {State : Type u}

/-!
## Definition 34: typed generators and finite observations
-/

/-- One heterogeneously typed outcome, tagged by the operation that produced it. -/
structure OutcomeEvent (coeffect : Coeffect.CoeffectAt State) where
  /-- The operation whose forward map ran. -/
  op : coeffect.Op
  /-- The outcome type is selected by `op`. -/
  value : coeffect.Outcome op

/-- A generator of one of Definition 34's operation transformation monoids. -/
inductive Letter (coeffect : Coeffect.CoeffectAt State) where
  /-- The forward map at one typed argument. -/
  | forward (op : coeffect.Op) (input : coeffect.Input op)
  /-- A concrete state-dependent inverse yielded at an enabled seed. -/
  | inverse (op : coeffect.Op) (input : coeffect.Input op) (seed : State)
      (enabled : coeffect.Enabled op input seed)

/-- Definition 34's finite word of transformation generators. -/
abbrev Test (coeffect : Coeffect.CoeffectAt State) := List (Letter coeffect)

/-- Add a forward outcome to a possibly undefined suffix observation. -/
def prependOutcome {coeffect : Coeffect.CoeffectAt State}
    (event : OutcomeEvent coeffect) :
    Option (List (OutcomeEvent coeffect)) → Option (List (OutcomeEvent coeffect))
  | none => none
  | some events => some (event :: events)

/-- Prefixing a fixed event is injective, including at undefined observations. -/
theorem prependOutcome_injective {coeffect : Coeffect.CoeffectAt State}
    (event : OutcomeEvent coeffect) : Function.Injective (prependOutcome event) := by
  intro left right equal
  cases left <;> cases right <;> simp [prependOutcome] at equal ⊢ <;> assumption

/-- Execute a finite operational test.

`none` means that a forward precondition failed. Successful observations retain only the
heterogeneous forward outcomes; intermediate states remain internal but determine later letters.
-/
def observe (coeffect : Coeffect.CoeffectAt State) :
    Test coeffect → State → Option (List (OutcomeEvent coeffect))
  | [], _ => some []
  | letter :: rest, state =>
      match letter with
      | .forward op input =>
          letI := coeffect.enabledDecidable op input state
          if enabled : coeffect.Enabled op input state then
            let result := coeffect.run op input state enabled
            prependOutcome ⟨op, result.2⟩ (observe coeffect rest result.1.after)
          else
            none
      | .inverse op input seed enabled =>
          let yielded := (coeffect.run op input seed enabled).1.undo
          observe coeffect rest (yielded state)

/-- Operational indistinguishability is agreement of all finite test observations. -/
def Indistinguishable (coeffect : Coeffect.CoeffectAt State) (left right : State) : Prop :=
  ∀ test, observe coeffect test left = observe coeffect test right

@[simp]
theorem observe_nil (coeffect : Coeffect.CoeffectAt State) (state : State) :
    observe coeffect [] state = some [] := rfl

/-- An enabled forward letter records its outcome and continues from its successor. -/
theorem observe_forward_of_enabled (coeffect : Coeffect.CoeffectAt State)
    (op : coeffect.Op) (input : coeffect.Input op) (state : State)
    (enabled : coeffect.Enabled op input state) (rest : Test coeffect) :
    observe coeffect (.forward op input :: rest) state =
      let result := coeffect.run op input state enabled
      prependOutcome ⟨op, result.2⟩ (observe coeffect rest result.1.after) := by
  simp [observe, enabled]

/-- A disabled forward letter makes the whole test undefined. -/
theorem observe_forward_of_disabled (coeffect : Coeffect.CoeffectAt State)
    (op : coeffect.Op) (input : coeffect.Input op) (state : State)
    (disabled : ¬coeffect.Enabled op input state) (rest : Test coeffect) :
    observe coeffect (.forward op input :: rest) state = none := by
  simp [observe, disabled]

/-- An inverse letter applies the concrete inverse yielded at its recorded seed. -/
@[simp]
theorem observe_inverse (coeffect : Coeffect.CoeffectAt State)
    (op : coeffect.Op) (input : coeffect.Input op) (seed : State)
    (enabled : coeffect.Enabled op input seed) (state : State) (rest : Test coeffect) :
    observe coeffect (.inverse op input seed enabled :: rest) state =
      observe coeffect rest ((coeffect.run op input seed enabled).1.undo state) := rfl

/-- One enabled forward letter observes exactly its singleton heterogeneous outcome. -/
theorem observe_single_forward_of_enabled (coeffect : Coeffect.CoeffectAt State)
    (op : coeffect.Op) (input : coeffect.Input op) (state : State)
    (enabled : coeffect.Enabled op input state) :
    observe coeffect [.forward op input] state =
      some [⟨op, (coeffect.run op input state enabled).2⟩] := by
  rw [observe_forward_of_enabled coeffect op input state enabled []]
  rfl

/-- Equality of equally tagged heterogeneous events implies equality of their values. -/
theorem OutcomeEvent.value_eq_of_eq {coeffect : Coeffect.CoeffectAt State}
    {op : coeffect.Op} {left right : coeffect.Outcome op}
    (equal : OutcomeEvent.mk op left = OutcomeEvent.mk op right) : left = right := by
  cases equal
  rfl

/-!
## The operational relation is an equivalence
-/

/-- Every state agrees with itself on every finite test. -/
theorem indistinguishable_refl (coeffect : Coeffect.CoeffectAt State) :
    ∀ state, Indistinguishable coeffect state state := by
  intro state test
  rfl

/-- Finite-test agreement is symmetric. -/
theorem indistinguishable_symm (coeffect : Coeffect.CoeffectAt State) :
    ∀ {left right}, Indistinguishable coeffect left right →
      Indistinguishable coeffect right left := by
  intro left right related test
  exact (related test).symm

/-- Finite-test agreement is transitive. -/
theorem indistinguishable_trans (coeffect : Coeffect.CoeffectAt State) :
    ∀ {left middle right},
      Indistinguishable coeffect left middle →
      Indistinguishable coeffect middle right →
      Indistinguishable coeffect left right := by
  intro left middle right leftRelated rightRelated test
  exact (leftRelated test).trans (rightRelated test)

/-- Definition 34 operational indistinguishability as a `Setoid`. -/
def indistinguishableSetoid (coeffect : Coeffect.CoeffectAt State) : Setoid State where
  r := Indistinguishable coeffect
  iseqv := {
    refl := indistinguishable_refl coeffect
    symm := indistinguishable_symm coeffect
    trans := indistinguishable_trans coeffect
  }

/-!
## Generator-level respect
-/

/-- The exact laws needed to preserve a relation through Definition 34's test letters.

Unlike `CoeffectAt.undo_respects`, `inverse_respects` applies the same concrete yielded inverse
to two related current states. That is exactly the fixed-generator action tested by one inverse
letter.
-/
structure GeneratorAdmissible (coeffect : Coeffect.CoeffectAt State)
    (relation : State → State → Prop) : Prop where
  /-- The candidate relation is an equivalence. -/
  equivalence : Equivalence relation
  /-- Related states agree on every forward precondition. -/
  enabled_respects : ∀ op input {left right}, relation left right →
    (coeffect.Enabled op input left ↔ coeffect.Enabled op input right)
  /-- Forward successors remain related. -/
  after_respects : ∀ op input {left right} (_related : relation left right)
    (leftEnabled : coeffect.Enabled op input left)
    (rightEnabled : coeffect.Enabled op input right),
    relation (coeffect.run op input left leftEnabled).1.after
      (coeffect.run op input right rightEnabled).1.after
  /-- Every fixed yielded inverse preserves the relation. -/
  inverse_respects : ∀ op input seed (enabled : coeffect.Enabled op input seed)
    {left right}, relation left right →
    relation ((coeffect.run op input seed enabled).1.undo left)
      ((coeffect.run op input seed enabled).1.undo right)
  /-- Related forward executions yield equal typed outcomes. -/
  outcome_respects : ∀ op input {left right} (_related : relation left right)
    (leftEnabled : coeffect.Enabled op input left)
    (rightEnabled : coeffect.Enabled op input right),
    (coeffect.run op input left leftEnabled).2 =
      (coeffect.run op input right rightEnabled).2

/-- Indistinguishable states agree on whether one forward generator is enabled. -/
theorem indistinguishable_enabled_iff (coeffect : Coeffect.CoeffectAt State)
    {left right : State} (related : Indistinguishable coeffect left right)
    (op : coeffect.Op) (input : coeffect.Input op) :
    coeffect.Enabled op input left ↔ coeffect.Enabled op input right := by
  constructor
  · intro leftEnabled
    letI := coeffect.enabledDecidable op input right
    by_cases rightEnabled : coeffect.Enabled op input right
    · exact rightEnabled
    · have observed := related [.forward op input]
      rw [observe_single_forward_of_enabled coeffect op input left leftEnabled] at observed
      rw [observe_forward_of_disabled coeffect op input right rightEnabled []] at observed
      cases observed
  · intro rightEnabled
    letI := coeffect.enabledDecidable op input left
    by_cases leftEnabled : coeffect.Enabled op input left
    · exact leftEnabled
    · have observed := related [.forward op input]
      rw [observe_forward_of_disabled coeffect op input left leftEnabled []] at observed
      rw [observe_single_forward_of_enabled coeffect op input right rightEnabled] at observed
      cases observed

/-- Indistinguishable enabled executions yield equal heterogeneous outcomes. -/
theorem indistinguishable_outcome_eq (coeffect : Coeffect.CoeffectAt State)
    {left right : State} (related : Indistinguishable coeffect left right)
    (op : coeffect.Op) (input : coeffect.Input op)
    (leftEnabled : coeffect.Enabled op input left)
    (rightEnabled : coeffect.Enabled op input right) :
    (coeffect.run op input left leftEnabled).2 =
      (coeffect.run op input right rightEnabled).2 := by
  have observed := related [.forward op input]
  rw [observe_single_forward_of_enabled coeffect op input left leftEnabled] at observed
  rw [observe_single_forward_of_enabled coeffect op input right rightEnabled] at observed
  have listsEqual := Option.some.inj observed
  have eventsEqual :
      OutcomeEvent.mk op (coeffect.run op input left leftEnabled).2 =
        OutcomeEvent.mk op (coeffect.run op input right rightEnabled).2 := by
    exact (List.cons.inj listsEqual).1
  exact OutcomeEvent.value_eq_of_eq eventsEqual

/-- Prefix closure makes forward successors operationally indistinguishable. -/
theorem indistinguishable_after (coeffect : Coeffect.CoeffectAt State)
    {left right : State} (related : Indistinguishable coeffect left right)
    (op : coeffect.Op) (input : coeffect.Input op)
    (leftEnabled : coeffect.Enabled op input left)
    (rightEnabled : coeffect.Enabled op input right) :
    Indistinguishable coeffect
      (coeffect.run op input left leftEnabled).1.after
      (coeffect.run op input right rightEnabled).1.after := by
  intro rest
  have observed := related (.forward op input :: rest)
  rw [observe_forward_of_enabled coeffect op input left leftEnabled rest] at observed
  rw [observe_forward_of_enabled coeffect op input right rightEnabled rest] at observed
  have outcomesEqual :=
    indistinguishable_outcome_eq coeffect related op input leftEnabled rightEnabled
  dsimp only at observed
  rw [outcomesEqual] at observed
  exact prependOutcome_injective
    ⟨op, (coeffect.run op input right rightEnabled).2⟩ observed

/-- Prefix closure makes every fixed yielded inverse preserve indistinguishability. -/
theorem indistinguishable_inverse (coeffect : Coeffect.CoeffectAt State)
    (op : coeffect.Op) (input : coeffect.Input op) (seed : State)
    (enabled : coeffect.Enabled op input seed) {left right : State}
    (related : Indistinguishable coeffect left right) :
    Indistinguishable coeffect
      ((coeffect.run op input seed enabled).1.undo left)
      ((coeffect.run op input seed enabled).1.undo right) := by
  intro rest
  simpa only [observe_inverse] using related (.inverse op input seed enabled :: rest)

/-- Lemma 35(1) for the exact fixed-generator test language. -/
theorem indistinguishable_admissible (coeffect : Coeffect.CoeffectAt State) :
    GeneratorAdmissible coeffect (Indistinguishable coeffect) where
  equivalence := {
    refl := indistinguishable_refl coeffect
    symm := indistinguishable_symm coeffect
    trans := indistinguishable_trans coeffect
  }
  enabled_respects := by
    intro op input left right related
    exact indistinguishable_enabled_iff coeffect related op input
  after_respects := by
    intro op input left right related leftEnabled rightEnabled
    exact indistinguishable_after coeffect related op input leftEnabled rightEnabled
  inverse_respects := by
    intro op input seed enabled left right related
    exact indistinguishable_inverse coeffect op input seed enabled related
  outcome_respects := by
    intro op input left right related leftEnabled rightEnabled
    exact indistinguishable_outcome_eq coeffect related op input leftEnabled rightEnabled

/-!
## Lemma 35(2): coarsest generator-admissible relation
-/

/-- Every generator-admissible relation is contained in operational indistinguishability. -/
theorem contained_in_indistinguishable (coeffect : Coeffect.CoeffectAt State)
    {relation : State → State → Prop} (admissible : GeneratorAdmissible coeffect relation)
    {left right : State} (related : relation left right) :
    Indistinguishable coeffect left right := by
  intro test
  induction test generalizing left right with
  | nil => rfl
  | cons letter rest induction =>
      cases letter with
      | forward op input =>
          have enabledIff := admissible.enabled_respects op input related
          letI := coeffect.enabledDecidable op input left
          by_cases leftEnabled : coeffect.Enabled op input left
          · have rightEnabled := enabledIff.mp leftEnabled
            rw [observe_forward_of_enabled coeffect op input left leftEnabled rest]
            rw [observe_forward_of_enabled coeffect op input right rightEnabled rest]
            have outcomesEqual :=
              admissible.outcome_respects op input related leftEnabled rightEnabled
            dsimp only
            rw [outcomesEqual]
            exact congrArg _
              (induction (admissible.after_respects op input related leftEnabled rightEnabled))
          · have rightDisabled : ¬coeffect.Enabled op input right := fun rightEnabled ↦
              leftEnabled (enabledIff.mpr rightEnabled)
            rw [observe_forward_of_disabled coeffect op input left leftEnabled rest]
            rw [observe_forward_of_disabled coeffect op input right rightDisabled rest]
      | inverse op input seed enabled =>
          rw [observe_inverse, observe_inverse]
          exact induction (admissible.inverse_respects op input seed enabled related)

/-- The relation originally declared by `CoeffectAt` is generator-admissible. -/
theorem declaredEquivalence_admissible (coeffect : Coeffect.CoeffectAt State) :
    GeneratorAdmissible coeffect coeffect.equivalence.r where
  equivalence := coeffect.equivalence.iseqv
  enabled_respects := coeffect.enabled_respects
  after_respects := coeffect.after_respects
  inverse_respects := fun op input seed enabled _ _ related ↦
    coeffect.undo_respects op input (coeffect.equivalence.iseqv.refl seed)
      enabled enabled related
  outcome_respects := coeffect.outcome_respects

/-- Every equivalence supplied by Definition 24 is below test indistinguishability. -/
theorem declaredEquivalence_contained (coeffect : Coeffect.CoeffectAt State)
    {left right : State} (related : coeffect.equivalence.r left right) :
    Indistinguishable coeffect left right :=
  contained_in_indistinguishable coeffect
    (declaredEquivalence_admissible coeffect) related

/-!
## The paired-inverse boundary
-/

/-- The additional law needed by the existing `CoeffectAt.undo_respects` field.

It compares the different inverses yielded at two operationally indistinguishable seeds. This is
strictly different from applying one fixed inverse generator at two states.
-/
def PairedInverseCoherent (coeffect : Coeffect.CoeffectAt State) : Prop :=
  ∀ op input {leftSeed rightSeed},
    Indistinguishable coeffect leftSeed rightSeed →
    ∀ (leftEnabled : coeffect.Enabled op input leftSeed)
      (rightEnabled : coeffect.Enabled op input rightSeed) {left right},
      Indistinguishable coeffect left right →
      Indistinguishable coeffect
        ((coeffect.run op input leftSeed leftEnabled).1.undo left)
        ((coeffect.run op input rightSeed rightEnabled).1.undo right)

/-- Under paired-inverse coherence, the same operations form a full `CoeffectAt` whose
equivalence is operational indistinguishability.
-/
def withOperationalEquivalence (coeffect : Coeffect.CoeffectAt State)
    (coherent : PairedInverseCoherent coeffect) : Coeffect.CoeffectAt State where
  equivalence := indistinguishableSetoid coeffect
  Op := coeffect.Op
  Input := coeffect.Input
  Outcome := coeffect.Outcome
  Enabled := coeffect.Enabled
  enabledDecidable := coeffect.enabledDecidable
  run := coeffect.run
  enabled_respects := by
    intro op input left right related
    exact indistinguishable_enabled_iff coeffect related op input
  after_respects := by
    intro op input left right related leftEnabled rightEnabled
    exact indistinguishable_after coeffect related op input leftEnabled rightEnabled
  undo_respects := by
    intro op input leftSeed rightSeed related leftEnabled rightEnabled left right currentsRelated
    exact coherent op input related leftEnabled rightEnabled currentsRelated
  outcome_respects := by
    intro op input left right related leftEnabled rightEnabled
    exact indistinguishable_outcome_eq coeffect related op input leftEnabled rightEnabled

/-!
## Integration with Definition 33 contexts
-/

/-- Use each key's Definition 34 tests as the equivalence family for Definition 33. -/
@[instance_reducible]
def operationalEquivalences {Key : Type u} {Value : Key → Type v}
    (coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)) :
    Coeffect.Observational.Equivalences Key Value :=
  fun key ↦ indistinguishableSetoid (coeffects key)

/-!
## Heterogeneous executable example
-/

namespace Example

/-- A state observed by a numeric operation and a string operation. -/
structure Machine where
  counter : Nat
  label : String
deriving DecidableEq, Repr

/-- Two operations with different input and outcome types. -/
inductive Op where
  | bump
  | rename
deriving DecidableEq, Repr

def Input : Op → Type
  | .bump => Unit
  | .rename => String

def Outcome : Op → Type
  | .bump => Nat
  | .rename => String

/-- Both operations have executable nontrivial domains. -/
def Enabled : (op : Op) → Input op → Machine → Prop
  | .bump, _, state => state.counter < 3
  | .rename, name, _ => name ≠ ""

def enabledDecidable (op : Op) (input : Input op) (state : Machine) :
    Decidable (Enabled op input state) :=
  match op with
  | .bump => inferInstanceAs (Decidable (state.counter < 3))
  | .rename => inferInstanceAs (Decidable ((show String from input) ≠ ""))

/-- Equality is an admissible starting equivalence for the operation implementation. -/
def machineSetoid : Setoid Machine where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

/-- The heterogeneous reversible operation suite. -/
def coeffect : Coeffect.CoeffectAt Machine where
  equivalence := machineSetoid
  Op := Op
  Input := Input
  Outcome := Outcome
  Enabled := Enabled
  enabledDecidable := enabledDecidable
  run op input before _enabled :=
    match op with
    | .bump =>
        ({ after := { before with counter := before.counter + 1 }
           undo := fun current ↦ { current with counter := current.counter - 1 }
           undo_after := by
             cases before
             simp }, before.counter + 1)
    | .rename =>
        ({ after := { before with label := input }
           undo := fun current ↦ { current with label := before.label }
           undo_after := by
             cases before
             rfl }, input)
  enabled_respects := by
    intro op input left right equal
    subst right
    rfl
  after_respects := by
    intro op input left right equal leftEnabled rightEnabled
    subst right
    rfl
  undo_respects := by
    intro op input left right equal leftEnabled rightEnabled leftCurrent rightCurrent currentEqual
    subst right
    subst rightCurrent
    rfl
  outcome_respects := by
    intro op input left right equal leftEnabled rightEnabled
    subst right
    rfl

def initial : Machine where
  counter := 0
  label := "old"

def blocked : Machine where
  counter := 3
  label := "old"

theorem initialBumpEnabled : Enabled .bump () initial := by
  change 0 < 3
  decide

theorem initialRenameEnabled : Enabled .rename "new" initial := by
  change "new" ≠ ""
  decide

/-- A word mixing both forward maps with a concrete state-dependent inverse generator. -/
def mixedTest : Test coeffect :=
  [.forward .bump (), .forward .rename "new",
    .inverse .rename "new" initial initialRenameEnabled]

def bumpOutcome : Outcome .bump := show Nat from 1
def renameOutcome : Outcome .rename := show String from "new"
def bumpEvent : OutcomeEvent coeffect := ⟨.bump, bumpOutcome⟩
def renameEvent : OutcomeEvent coeffect := ⟨.rename, renameOutcome⟩

example : observe coeffect mixedTest initial = some [bumpEvent, renameEvent] := rfl

/-- Failed-precondition behavior is observable and executable. -/
example : observe coeffect [.forward .bump ()] blocked = none := rfl

/-- Equality is contained in the operational relation by Lemma 35(2). -/
example : Indistinguishable coeffect initial initial :=
  declaredEquivalence_contained coeffect rfl

/-- A one-letter heterogeneous outcome separates counter `0` from counter `1`. -/
theorem initial_not_indistinguishable_from_bumped :
    ¬Indistinguishable coeffect initial { initial with counter := 1 } := by
  intro related
  have observed := related [.forward .bump ()]
  simp [observe, coeffect, Enabled, initial] at observed
  have listsEqual := Option.some.inj observed
  have eventsEqual := (List.cons.inj listsEqual).1
  have valuesEqual := OutcomeEvent.value_eq_of_eq eventsEqual
  change (1 : Nat) = 2 at valuesEqual
  omega

/-! The operational setoid can be installed as one key of Definition 33's family. -/

inductive Key where
  | machine
  | name
deriving DecidableEq, Repr

def Value : Key → Type
  | .machine => Machine
  | .name => String

def nameCoeffect : Coeffect.CoeffectAt String where
  equivalence := {
    r := Eq
    iseqv := {
      refl := Eq.refl
      symm := Eq.symm
      trans := Eq.trans
    }
  }
  Op := Empty
  Input := Empty.elim
  Outcome := Empty.elim
  Enabled := fun op ↦ Empty.elim op
  enabledDecidable := fun op ↦ Empty.elim op
  run := fun op ↦ Empty.elim op
  enabled_respects := fun op ↦ Empty.elim op
  after_respects := fun op ↦ Empty.elim op
  undo_respects := fun op ↦ Empty.elim op
  outcome_respects := fun op ↦ Empty.elim op

def coeffects : (key : Key) → Coeffect.CoeffectAt (Value key)
  | .machine => coeffect
  | .name => nameCoeffect

@[instance_reducible]
def equivalences : Coeffect.Observational.Equivalences Key Value :=
  operationalEquivalences coeffects

def machineValue : Value .machine := initial
def alice : Value .name := show String from "alice"
def bob : Value .name := show String from "bob"

def leftContext : Coeffect.Context Key Value :=
  Coeffect.setAt (Coeffect.setAt Coeffect.empty .machine machineValue) .name alice

def renamedContext : Coeffect.Context Key Value :=
  Coeffect.setAt (Coeffect.setAt Coeffect.empty .machine machineValue) .name bob

/-- With no operations at `name`, Definition 34 cannot distinguish its two string values. -/
theorem names_indistinguishable : Indistinguishable nameCoeffect alice bob := by
  intro test
  cases test with
  | nil => rfl
  | cons letter rest =>
      cases letter with
      | forward op _ => exact Empty.elim op
      | inverse op _ _ _ => exact Empty.elim op

/-- Definition 33 uses the operational setoid independently at each heterogeneous key. -/
theorem leftContext_related_renamedContext :
    Coeffect.Observational.Related equivalences leftContext renamedContext := by
  intro key
  cases key with
  | machine =>
      exact Coeffect.Observational.OptionRelated.some
        (indistinguishable_refl coeffect initial)
  | name =>
      exact Coeffect.Observational.OptionRelated.some names_indistinguishable

end Example

/-!
## A finite counterexample to deriving paired-inverse coherence

The hidden bit below affects which inverse an operation yields but is never directly observed.
Every fixed inverse generator acts uniformly on two states with the same visible bit. Two
different inverses yielded at hidden-different seeds can nevertheless disagree visibly. This
separates Definition 34's same-letter tests from the stronger paired field in `CoeffectAt`.
-/

namespace PairedGap

structure GapState where
  hidden : Bool
  visible : Bool
deriving DecidableEq, Repr

inductive Op where
  | prepare
  | read
deriving DecidableEq, Repr

def Input : Op → Type
  | .prepare => Unit
  | .read => Unit

def Outcome : Op → Type
  | .prepare => Unit
  | .read => Bool

def Enabled : (op : Op) → Input op → GapState → Prop
  | .prepare, _, _ => True
  | .read, _, _ => True

def enabledDecidable (op : Op) (input : Input op) (state : GapState) :
    Decidable (Enabled op input state) := by
  cases op <;> exact isTrue trivial

def equalitySetoid : Setoid GapState where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

/-- `prepare` hides the visible bit and yields an inverse whose off-successor behavior also
depends on the seed's hidden bit. `read` exposes only the visible bit.
-/
def coeffect : Coeffect.CoeffectAt GapState where
  equivalence := equalitySetoid
  Op := Op
  Input := Input
  Outcome := Outcome
  Enabled := Enabled
  enabledDecidable := enabledDecidable
  run op _input before _enabled :=
    match op with
    | .prepare =>
        ({ after := { before with visible := false }
           undo := fun current ↦
             { current with
               visible := if current.visible then before.hidden else before.visible }
           undo_after := by
             cases before
             rfl }, ())
    | .read =>
        ({ after := before
           undo := id
           undo_after := rfl }, before.visible)
  enabled_respects := by
    intro op input left right equal
    subst right
    rfl
  after_respects := by
    intro op input left right equal leftEnabled rightEnabled
    subst right
    rfl
  undo_respects := by
    intro op input left right equal leftEnabled rightEnabled leftCurrent rightCurrent currentEqual
    subst right
    subst rightCurrent
    rfl
  outcome_respects := by
    intro op input left right equal leftEnabled rightEnabled
    subst right
    rfl

/-- The candidate relation deliberately forgets the hidden bit. -/
def SameVisible (left right : GapState) : Prop := left.visible = right.visible

/-- Every fixed Definition 34 generator preserves equality of visible bits. -/
theorem sameVisible_admissible : GeneratorAdmissible coeffect SameVisible where
  equivalence := {
    refl := fun _ ↦ rfl
    symm := fun related ↦ related.symm
    trans := fun leftRelated rightRelated ↦ leftRelated.trans rightRelated
  }
  enabled_respects := by
    intro op input left right related
    cases op <;> constructor <;> intro <;> trivial
  after_respects := by
    intro op input left right related leftEnabled rightEnabled
    cases op with
    | prepare => rfl
    | read => exact related
  inverse_respects := by
    intro op input seed enabled left right related
    cases op with
    | prepare =>
        change (if left.visible then seed.hidden else seed.visible) =
          (if right.visible then seed.hidden else seed.visible)
        rw [related]
    | read => exact related
  outcome_respects := by
    intro op input left right related leftEnabled rightEnabled
    cases op with
    | prepare => rfl
    | read => exact related

def leftSeed : GapState where
  hidden := false
  visible := true

def rightSeed : GapState where
  hidden := true
  visible := true

/-- Lemma 35(2) makes the hidden-different seeds operationally indistinguishable. -/
theorem seeds_indistinguishable : Indistinguishable coeffect leftSeed rightSeed :=
  contained_in_indistinguishable coeffect sameVisible_admissible rfl

/-- Nevertheless, the paired inverses yielded at those seeds can produce visibly distinct
states from one common current state.
-/
theorem pairedInverseCoherent_fails : ¬PairedInverseCoherent coeffect := by
  intro coherent
  have currentsRelated : Indistinguishable coeffect leftSeed leftSeed :=
    indistinguishable_refl coeffect leftSeed
  have inversesRelated :=
    coherent .prepare () seeds_indistinguishable trivial trivial currentsRelated
  have observed := inversesRelated [.forward .read ()]
  simp [observe, coeffect, Enabled, leftSeed, rightSeed] at observed
  have listsEqual := Option.some.inj observed
  have eventsEqual := (List.cons.inj listsEqual).1
  have valuesEqual := OutcomeEvent.value_eq_of_eq eventsEqual
  change false = true at valuesEqual
  cases valuesEqual

end PairedGap

end Cordis.OperationalEquivalence
