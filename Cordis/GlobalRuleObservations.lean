import Cordis.GlobalRuleInvariance

/-!
# Assumption-free lifecycle observations under rule equivalence

This module builds the maximal observation layer available from two well-formed states related by
`GlobalRelations.RuleRelated`. It proves exact matched control, active-provider name transport,
dependent target-view transport, resolution and reliance invariance, quiescence invariance, and
the structural guards shared by L-Begin, L-Leave, L-Divert, and L-Unload.

No theorem executes a lifecycle rule. Iterator results, landing evidence, run errors,
registration-oracle decisions, recovery admission, and inertia remain separate assumptions. In
particular, the earlier ambient-sensitive inertia counterexample still prevents full Lemma 55.

The module is a bounded source-faithful substrate for CORDIS paper Lemma 55 at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`; it is not the ten-rule bisimulation itself.

One future L-Finish seam is explicit: matched active fibers have related private tables, but a
reloading owner's table is unobserved. A landing that makes the owner active must separately
relate the two yielded `afterFiber.table` values; rule observation cannot reconstruct that law.
-/

set_option autoImplicit false

namespace Cordis.GlobalRuleObservations

open Cordis.GlobalRegistry Cordis.GlobalRelations Cordis.GlobalRuleInvariance

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-!
## Matched dependent control
-/

theorem controlPhase_heq
    {left right : FiberControl catalog} (equal : left = right) : HEq left.phase right.phase := by
  cases equal
  rfl

theorem controlPhase_eq
    {left right : FiberControl catalog} (equal : left = right) :
    congrArg FiberControl.component equal ▸ left.phase = right.phase := by
  cases equal
  rfl

theorem fiberControl_phase_heq
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) : HEq left.phase right.phase := by
  exact controlPhase_heq controls

theorem fiberControl_phase_eq
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) :
    fiberControl_component_eq controls ▸ left.phase = right.phase := by
  have proofEq : fiberControl_component_eq controls =
      congrArg FiberControl.component controls := Subsingleton.elim _ _
  rw [proofEq]
  exact controlPhase_eq controls

/-- The existing exact-control lookup, exposed under an observation-specific name. -/
def matchedFiber
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    {name : sig.Name} {leftFiber : Fiber catalog}
    (related : RuleRelated values left right)
    (leftPresent : left.registry name = some leftFiber) :
    FiberMatch values left right name leftFiber :=
  matchFiber related leftPresent

/-!
## Active provider names
-/

theorem activeProvider_forward
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {key : sig.Key} {name : sig.Name} :
    ActiveProvider left key name → ActiveProvider right key name := by
  rintro ⟨leftFiber, leftPresent, leftActive, leftValuePresent⟩
  let aligned := matchedFiber related leftPresent
  have rightActive : aligned.peerFiber.Active :=
    (fiberControl_active_iff aligned.control_eq).1 leftActive
  cases leftValueEq : leftFiber.table key with
  | none => simp [leftValueEq] at leftValuePresent
  | some leftValue =>
      have leftContext : activeContext left key = some leftValue :=
        (activeContext_value_iff leftWf).2
          ⟨name, leftFiber, leftPresent, leftActive, leftValueEq⟩
      have contextRelated := related.1 key
      rw [leftContext] at contextRelated
      cases rightContextEq : activeContext right key with
      | none => simp [OptionRelated, rightContextEq] at contextRelated
      | some rightValue =>
          obtain ⟨rightName, rightFiber, rightPresent, otherActive, rightValueEq⟩ :=
            (activeContext_value_iff rightWf).1 rightContextEq
          have leftDeclared := leftFiber.table_within_provision key (by simp [leftValueEq])
          have alignedDeclared :
              key ∈ (catalog.declaration aligned.peerFiber.component).provision := by
            have componentEq := fiberControl_component_eq aligned.control_eq
            simpa [componentEq] using leftDeclared
          have rightDeclared := rightFiber.table_within_provision key (by simp [rightValueEq])
          have namesEqual : name = rightName :=
            rightWf.provisions_unique name aligned.peerFiber rightName rightFiber key
              aligned.peer_present rightPresent alignedDeclared rightDeclared
          subst rightName
          rw [aligned.peer_present] at rightPresent
          have fibersEqual := Option.some.inj rightPresent
          subst rightFiber
          exact ⟨aligned.peerFiber, aligned.peer_present, rightActive,
            by simp [rightValueEq]⟩

theorem activeProvider_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (key : sig.Key) (name : sig.Name) :
    ActiveProvider left key name ↔ ActiveProvider right key name := by
  constructor
  · exact activeProvider_forward leftWf rightWf related
  · exact activeProvider_forward rightWf leftWf (ruleRelated_symm related)

/-- Pointwise table observation for fibers that are active at the same matched name. -/
def FiberTableRelated
    (values : ValueSetoids sig) (left right : Fiber catalog) : Prop :=
  ∀ key, OptionRelated (values.relation key) (left.table key) (right.table key)

theorem activeFiberTables_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (leftActive : leftFiber.Active) : FiberTableRelated values leftFiber rightFiber := by
  have rightActive := (fiberControl_active_iff controls).1 leftActive
  intro key
  cases leftValueEq : leftFiber.table key with
  | none =>
      cases rightValueEq : rightFiber.table key with
      | none => trivial
      | some rightValue =>
          have rightProvider : ActiveProvider right key name :=
            ⟨rightFiber, rightPresent, rightActive, by simp [rightValueEq]⟩
          obtain ⟨leftWitness, leftLookup, active, present⟩ :=
            (activeProvider_iff leftWf rightWf related key name).2 rightProvider
          rw [leftPresent] at leftLookup
          have equal := Option.some.inj leftLookup
          subst leftWitness
          simp [leftValueEq] at present
  | some leftValue =>
      cases rightValueEq : rightFiber.table key with
      | none =>
          have leftProvider : ActiveProvider left key name :=
            ⟨leftFiber, leftPresent, leftActive, by simp [leftValueEq]⟩
          obtain ⟨rightWitness, rightLookup, active, present⟩ :=
            (activeProvider_iff leftWf rightWf related key name).1 leftProvider
          rw [rightPresent] at rightLookup
          have equal := Option.some.inj rightLookup
          subst rightWitness
          simp [rightValueEq] at present
      | some rightValue =>
          have leftContext : activeContext left key = some leftValue :=
            (activeContext_value_iff leftWf).2
              ⟨name, leftFiber, leftPresent, leftActive, leftValueEq⟩
          have rightContext : activeContext right key = some rightValue :=
            (activeContext_value_iff rightWf).2
              ⟨name, rightFiber, rightPresent, rightActive, rightValueEq⟩
          simpa [OptionRelated, leftContext, rightContext] using related.1 key

/-!
## Dependent committed views and targets
-/

def transportCommitted
    {left right : sig.ComponentId} (componentEq : left = right)
    (view : CommittedView (catalog.declaration left)) :
    CommittedView (catalog.declaration right) :=
  componentEq ▸ view

def transportDeclared
    {left right : sig.ComponentId} (componentEq : left = right)
    (declared : DeclaredKey (catalog.declaration left)) :
    DeclaredKey (catalog.declaration right) :=
  componentEq ▸ declared

@[simp]
theorem transportCommitted_rfl
    {component : sig.ComponentId}
    (view : CommittedView (catalog.declaration component)) :
    transportCommitted (catalog := catalog) rfl view = view := rfl

@[simp]
theorem transportDeclared_rfl
    {component : sig.ComponentId}
    (declared : DeclaredKey (catalog.declaration component)) :
    transportDeclared (catalog := catalog) rfl declared = declared := rfl

theorem transportCommitted_provider
    {left right : sig.ComponentId} (componentEq : left = right)
    (view : CommittedView (catalog.declaration left))
    (declared : DeclaredKey (catalog.declaration left)) :
    (transportCommitted componentEq view).provider
        (transportDeclared componentEq declared) = view.provider declared := by
  cases componentEq
  rfl

@[simp]
theorem transportCommitted_roundtrip
    {left right : sig.ComponentId} (componentEq : left = right)
    (view : CommittedView (catalog.declaration right)) :
    transportCommitted componentEq (transportCommitted componentEq.symm view) = view := by
  cases componentEq
  rfl

@[simp]
theorem transportDeclared_roundtrip
    {left right : sig.ComponentId} (componentEq : left = right)
    (declared : DeclaredKey (catalog.declaration right)) :
    transportDeclared componentEq (transportDeclared componentEq.symm declared) = declared := by
  cases componentEq
  rfl

@[simp]
theorem transportDeclared_key
    {left right : sig.ComponentId} (componentEq : left = right)
    (declared : DeclaredKey (catalog.declaration left)) :
    (transportDeclared componentEq declared).key = declared.key := by
  cases componentEq
  rfl

theorem isTargetView_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (view : CommittedView (catalog.declaration leftFiber.component)) :
    IsTargetView left name leftFiber view ↔
      IsTargetView right name rightFiber
        (transportCommitted (fiberControl_component_eq controls) view) := by
  have componentEq := fiberControl_component_eq controls
  constructor
  · intro target
    exact {
      present := rightPresent
      not_retired := (fiberControl_retired_eq controls).symm.trans target.not_retired
      resolves_active := by
        intro rightDeclared
        let leftDeclared := transportDeclared componentEq.symm rightDeclared
        have providerEq :
            (transportCommitted componentEq view).provider rightDeclared =
              view.provider leftDeclared := by
          calc
            (transportCommitted componentEq view).provider rightDeclared =
                (transportCommitted componentEq view).provider
                  (transportDeclared componentEq leftDeclared) := by
                    rw [transportDeclared_roundtrip]
            _ = view.provider leftDeclared :=
              transportCommitted_provider componentEq view leftDeclared
        rw [providerEq]
        simpa [leftDeclared] using
          (activeProvider_iff leftWf rightWf related leftDeclared.key
            (view.provider leftDeclared)).1 (target.resolves_active leftDeclared)
    }
  · intro target
    exact {
      present := leftPresent
      not_retired := (fiberControl_retired_eq controls).trans target.not_retired
      resolves_active := by
        intro leftDeclared
        let rightDeclared := transportDeclared componentEq leftDeclared
        have providerEq :
            (transportCommitted componentEq view).provider rightDeclared =
              view.provider leftDeclared :=
          transportCommitted_provider componentEq view leftDeclared
        have rightActive := target.resolves_active rightDeclared
        rw [providerEq] at rightActive
        simpa [rightDeclared] using
          (activeProvider_iff leftWf rightWf related rightDeclared.key
            (view.provider leftDeclared)).2 rightActive
    }

theorem targetView_some_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (view : CommittedView (catalog.declaration leftFiber.component)) :
    targetView left name leftFiber = some view ↔
      targetView right name rightFiber =
        some (transportCommitted (fiberControl_component_eq controls) view) := by
  constructor
  · intro leftTarget
    exact targetView_eq_of_isTarget rightWf
      ((isTargetView_iff leftWf rightWf related leftPresent rightPresent controls view).1
        (targetView_sound leftWf leftTarget))
  · intro rightTarget
    exact targetView_eq_of_isTarget leftWf
      ((isTargetView_iff leftWf rightWf related leftPresent rightPresent controls view).2
        (targetView_sound rightWf rightTarget))

theorem targetView_none_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    targetView left name leftFiber = none ↔ targetView right name rightFiber = none := by
  have componentEq := fiberControl_component_eq controls
  constructor
  · intro leftNone
    cases rightEq : targetView right name rightFiber with
    | none => rfl
    | some rightView =>
        let leftView := transportCommitted componentEq.symm rightView
        have leftSome :=
          (targetView_some_iff leftWf rightWf related leftPresent rightPresent controls
            leftView).2 (by simpa [leftView] using rightEq)
        rw [leftNone] at leftSome
        cases leftSome
  · intro rightNone
    cases leftEq : targetView left name leftFiber with
    | none => rfl
    | some leftView =>
        have rightSome :=
          (targetView_some_iff leftWf rightWf related leftPresent rightPresent controls
            leftView).1 leftEq
        rw [rightNone] at rightSome
        cases rightSome

theorem targetView_transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Option.map (transportCommitted (fiberControl_component_eq controls))
        (targetView left name leftFiber) = targetView right name rightFiber := by
  cases leftEq : targetView left name leftFiber with
  | none =>
      have rightNone :=
        (targetView_none_iff leftWf rightWf related leftPresent rightPresent controls).1 leftEq
      simp [rightNone]
  | some view =>
      have rightSome :=
        (targetView_some_iff leftWf rightWf related leftPresent rightPresent controls view).1
          leftEq
      simp [rightSome]

theorem targetView_changed_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (view : CommittedView (catalog.declaration leftFiber.component)) :
    targetView left name leftFiber ≠ some view ↔
      targetView right name rightFiber ≠
        some (transportCommitted (fiberControl_component_eq controls) view) :=
  not_congr
    (targetView_some_iff leftWf rightWf related leftPresent rightPresent controls view)

/-!
## Committed resolutions and reliance
-/

theorem phaseCommitted_transport
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase) :
    Option.map (transportCommitted componentEq) leftPhase.committed? =
      rightPhase.committed? := by
  cases componentEq
  subst rightPhase
  cases leftPhase <;> rfl

theorem fiberControl_committed_eq
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) :
    Option.map (transportCommitted (fiberControl_component_eq controls))
        left.phase.committed? = right.phase.committed? :=
  phaseCommitted_transport (fiberControl_component_eq controls) left.phase right.phase
    (fiberControl_phase_eq controls)

theorem resolvesTo_forward
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) (provider : sig.Name) :
    ResolvesTo left provider → ResolvesTo right provider := by
  rintro ⟨leftCommitted, leftCommittedEq, leftDeclared, providerEq⟩
  let componentEq := fiberControl_component_eq controls
  let rightCommitted := transportCommitted componentEq leftCommitted
  have committedControls := fiberControl_committed_eq controls
  have rightCommittedEq : right.phase.committed? = some rightCommitted := by
    rw [← committedControls, leftCommittedEq]
    rfl
  let rightDeclared := transportDeclared componentEq leftDeclared
  have transportedProvider : rightCommitted.provider rightDeclared =
      leftCommitted.provider leftDeclared :=
    transportCommitted_provider componentEq leftCommitted leftDeclared
  exact ⟨rightCommitted, rightCommittedEq, rightDeclared,
    transportedProvider.trans providerEq⟩

theorem resolvesTo_iff
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) (provider : sig.Name) :
    ResolvesTo left provider ↔ ResolvesTo right provider := by
  constructor
  · exact resolvesTo_forward controls provider
  · exact resolvesTo_forward controls.symm provider

theorem relied_forward
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (provider : sig.Name) :
    Relied left provider → Relied right provider := by
  rintro ⟨consumerName, leftConsumer, leftPresent, different, installed, resolves⟩
  let aligned := matchedFiber related leftPresent
  exact ⟨consumerName, aligned.peerFiber, aligned.peer_present, different,
    (fiberControl_installed_iff aligned.control_eq).1 installed,
    (resolvesTo_iff aligned.control_eq provider).1 resolves⟩

theorem relied_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (provider : sig.Name) :
    Relied left provider ↔ Relied right provider := by
  constructor
  · exact relied_forward related provider
  · exact relied_forward (ruleRelated_symm related) provider

theorem notRelied_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (provider : sig.Name) :
    (¬Relied left provider) ↔ (¬Relied right provider) :=
  not_congr (relied_iff related provider)

/-!
## Exact phase patterns and quiescence
-/

theorem phaseInactive_iff
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase) (outcome : Option sig.Error) :
    leftPhase = .inactive outcome ↔ rightPhase = .inactive outcome := by
  cases componentEq
  subst rightPhase
  rfl

theorem phaseReloading_iff
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) :
    leftPhase = .reloading code undos committed ↔
      rightPhase = .reloading code undos (transportCommitted componentEq committed) := by
  cases componentEq
  subst rightPhase
  rfl

theorem phaseActive_iff
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) :
    leftPhase = .active undos committed ↔
      rightPhase = .active undos (transportCommitted componentEq committed) := by
  cases componentEq
  subst rightPhase
  rfl

theorem phaseUnloading_iff
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) (outcome : Option sig.Error) :
    leftPhase = .unloading undos committed outcome ↔
      rightPhase = .unloading undos (transportCommitted componentEq committed) outcome := by
  cases componentEq
  subst rightPhase
  rfl

theorem fiberControl_inactive_iff
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right) (outcome : Option sig.Error) :
    left.phase = .inactive outcome ↔ right.phase = .inactive outcome :=
  phaseInactive_iff (fiberControl_component_eq controls) left.phase right.phase
    (fiberControl_phase_eq controls) outcome

theorem fiberControl_reloading_iff
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left.component)) :
    left.phase = .reloading code undos committed ↔
      right.phase = .reloading code undos
        (transportCommitted (fiberControl_component_eq controls) committed) :=
  phaseReloading_iff (fiberControl_component_eq controls) left.phase right.phase
    (fiberControl_phase_eq controls) code undos committed

theorem fiberControl_active_phase_iff
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left.component)) :
    left.phase = .active undos committed ↔
      right.phase = .active undos
        (transportCommitted (fiberControl_component_eq controls) committed) :=
  phaseActive_iff (fiberControl_component_eq controls) left.phase right.phase
    (fiberControl_phase_eq controls) undos committed

theorem fiberControl_unloading_iff
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left.component))
    (outcome : Option sig.Error) :
    left.phase = .unloading undos committed outcome ↔
      right.phase = .unloading undos
        (transportCommitted (fiberControl_component_eq controls) committed) outcome :=
  phaseUnloading_iff (fiberControl_component_eq controls) left.phase right.phase
    (fiberControl_phase_eq controls) undos committed outcome

def QuiescentAt
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) : Prop :=
  match fiber.phase with
  | .inactive outcome => outcome.isSome = true ∨ targetView state name fiber = none
  | .active _ committed => targetView state name fiber = some committed
  | .reloading _ _ _ => False
  | .unloading _ _ _ => False

theorem quiescentAt_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    QuiescentAt left name leftFiber ↔ QuiescentAt right name rightFiber := by
  cases leftPhase : leftFiber.phase with
  | inactive outcome =>
      have rightPhase := (fiberControl_inactive_iff controls outcome).1 leftPhase
      rw [show QuiescentAt left name leftFiber =
          (outcome.isSome = true ∨ targetView left name leftFiber = none) by
        simp [QuiescentAt, leftPhase]]
      rw [show QuiescentAt right name rightFiber =
          (outcome.isSome = true ∨ targetView right name rightFiber = none) by
        simp [QuiescentAt, rightPhase]]
      exact or_congr Iff.rfl
        (targetView_none_iff leftWf rightWf related leftPresent rightPresent controls)
  | reloading code undos committed =>
      have rightPhase :=
        (fiberControl_reloading_iff controls code undos committed).1 leftPhase
      simp [QuiescentAt, leftPhase, rightPhase]
  | active undos committed =>
      have rightPhase :=
        (fiberControl_active_phase_iff controls undos committed).1 leftPhase
      rw [show QuiescentAt left name leftFiber =
          (targetView left name leftFiber = some committed) by
        simp [QuiescentAt, leftPhase]]
      rw [show QuiescentAt right name rightFiber =
          (targetView right name rightFiber =
            some (transportCommitted (fiberControl_component_eq controls) committed)) by
        simp [QuiescentAt, rightPhase]]
      exact targetView_some_iff leftWf rightWf related leftPresent rightPresent controls
        committed
  | unloading undos committed outcome =>
      have rightPhase :=
        (fiberControl_unloading_iff controls undos committed outcome).1 leftPhase
      simp [QuiescentAt, leftPhase, rightPhase]

theorem quiescent_forward
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right) : Quiescent left → Quiescent right := by
  intro leftQuiescent name rightFiber rightPresent
  let aligned := matchedFiber (ruleRelated_symm related) rightPresent
  have leftAt := leftQuiescent name aligned.peerFiber aligned.peer_present
  change QuiescentAt left name aligned.peerFiber at leftAt
  change QuiescentAt right name rightFiber
  exact (quiescentAt_iff leftWf rightWf related aligned.peer_present rightPresent
    aligned.control_eq.symm).1 leftAt

theorem quiescent_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right) : Quiescent left ↔ Quiescent right := by
  constructor
  · exact quiescent_forward leftWf rightWf related
  · exact quiescent_forward rightWf leftWf (ruleRelated_symm related)

/-!
## Structural lifecycle guards
-/

structure BeginGuard
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) where
  present : state.registry name = some fiber
  committed : CommittedView (catalog.declaration fiber.component)
  entry : fiber.phase = .inactive none
  target : targetView state name fiber = some committed

structure ReloadingTargetGuard
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) where
  present : state.registry name = some fiber
  code : sig.IteratorCode
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  phase : fiber.phase = .reloading code undos committed
  target : targetView state name fiber = some committed

structure LeaveGuard
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) where
  present : state.registry name = some fiber
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  phase : fiber.phase = .active undos committed
  target_changed : targetView state name fiber ≠ some committed

structure DivertGuard
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) where
  present : state.registry name = some fiber
  code : sig.IteratorCode
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  phase : fiber.phase = .reloading code undos committed
  target_changed : targetView state name fiber ≠ some committed

structure UnloadGuard
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) where
  present : state.registry name = some fiber
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  outcome : Option sig.Error
  phase : fiber.phase = .unloading undos committed outcome
  not_relied : ¬Relied state name

def BeginGuard.transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (guard : BeginGuard left name leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    BeginGuard right name rightFiber := {
  present := rightPresent
  committed := transportCommitted (fiberControl_component_eq controls) guard.committed
  entry := (fiberControl_inactive_iff controls none).1 guard.entry
  target := (targetView_some_iff leftWf rightWf related guard.present rightPresent controls
    guard.committed).1 guard.target
}

def ReloadingTargetGuard.transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (guard : ReloadingTargetGuard left name leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    ReloadingTargetGuard right name rightFiber := {
  present := rightPresent
  code := guard.code
  undos := guard.undos
  committed := transportCommitted (fiberControl_component_eq controls) guard.committed
  phase := (fiberControl_reloading_iff controls guard.code guard.undos guard.committed).1
    guard.phase
  target := (targetView_some_iff leftWf rightWf related guard.present rightPresent controls
    guard.committed).1 guard.target
}

def LeaveGuard.transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (guard : LeaveGuard left name leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    LeaveGuard right name rightFiber := {
  present := rightPresent
  undos := guard.undos
  committed := transportCommitted (fiberControl_component_eq controls) guard.committed
  phase := (fiberControl_active_phase_iff controls guard.undos guard.committed).1 guard.phase
  target_changed :=
    (targetView_changed_iff leftWf rightWf related guard.present rightPresent controls
      guard.committed).1 guard.target_changed
}

def DivertGuard.transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (guard : DivertGuard left name leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    DivertGuard right name rightFiber := {
  present := rightPresent
  code := guard.code
  undos := guard.undos
  committed := transportCommitted (fiberControl_component_eq controls) guard.committed
  phase := (fiberControl_reloading_iff controls guard.code guard.undos guard.committed).1
    guard.phase
  target_changed :=
    (targetView_changed_iff leftWf rightWf related guard.present rightPresent controls
      guard.committed).1 guard.target_changed
}

def UnloadGuard.transport
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (guard : UnloadGuard left name leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    UnloadGuard right name rightFiber := {
  present := rightPresent
  undos := guard.undos
  committed := transportCommitted (fiberControl_component_eq controls) guard.committed
  outcome := guard.outcome
  phase := (fiberControl_unloading_iff controls guard.undos guard.committed guard.outcome).1
    guard.phase
  not_relied := (notRelied_iff related name).1 guard.not_relied
}

theorem beginGuard_nonempty_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Nonempty (BeginGuard left name leftFiber) ↔
      Nonempty (BeginGuard right name rightFiber) := by
  constructor
  · rintro ⟨guard⟩
    exact ⟨guard.transport leftWf rightWf related rightPresent controls⟩
  · rintro ⟨guard⟩
    exact ⟨guard.transport rightWf leftWf (ruleRelated_symm related) leftPresent controls.symm⟩

theorem reloadingTargetGuard_nonempty_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Nonempty (ReloadingTargetGuard left name leftFiber) ↔
      Nonempty (ReloadingTargetGuard right name rightFiber) := by
  constructor
  · rintro ⟨guard⟩
    exact ⟨guard.transport leftWf rightWf related rightPresent controls⟩
  · rintro ⟨guard⟩
    exact ⟨guard.transport rightWf leftWf (ruleRelated_symm related) leftPresent controls.symm⟩

theorem leaveGuard_nonempty_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Nonempty (LeaveGuard left name leftFiber) ↔
      Nonempty (LeaveGuard right name rightFiber) := by
  constructor
  · rintro ⟨guard⟩
    exact ⟨guard.transport leftWf rightWf related rightPresent controls⟩
  · rintro ⟨guard⟩
    exact ⟨guard.transport rightWf leftWf (ruleRelated_symm related) leftPresent controls.symm⟩

theorem divertGuard_nonempty_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Nonempty (DivertGuard left name leftFiber) ↔
      Nonempty (DivertGuard right name rightFiber) := by
  constructor
  · rintro ⟨guard⟩
    exact ⟨guard.transport leftWf rightWf related rightPresent controls⟩
  · rintro ⟨guard⟩
    exact ⟨guard.transport rightWf leftWf (ruleRelated_symm related) leftPresent controls.symm⟩

theorem unloadGuard_nonempty_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    {name : sig.Name} {leftFiber rightFiber : Fiber catalog}
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    Nonempty (UnloadGuard left name leftFiber) ↔
      Nonempty (UnloadGuard right name rightFiber) := by
  constructor
  · rintro ⟨guard⟩
    exact ⟨guard.transport related rightPresent controls⟩
  · rintro ⟨guard⟩
    exact ⟨guard.transport (ruleRelated_symm related) leftPresent controls.symm⟩

/-!
## Unequal-table heterogeneous example
-/

namespace HeterogeneousExample

abbrev values := Cordis.GlobalRuleInvariance.HeterogeneousExample.values
abbrev leftState := Cordis.GlobalRuleInvariance.HeterogeneousExample.leftState
abbrev rightState := Cordis.GlobalRuleInvariance.HeterogeneousExample.rightState
abbrev leftFiber := Cordis.GlobalRegistry.Example.activeProviderFiber
abbrev rightFiber := Cordis.GlobalRuleInvariance.HeterogeneousExample.rightProviderFiber

theorem leftPresent : leftState.registry 0 = some leftFiber := rfl

theorem rightPresent : rightState.registry 0 = some rightFiber := rfl

theorem controls : fiberControl leftFiber = fiberControl rightFiber := rfl

theorem provider_counter_iff :
    ActiveProvider leftState .counter 0 ↔ ActiveProvider rightState .counter 0 :=
  activeProvider_iff
    Cordis.GlobalRuleInvariance.HeterogeneousExample.leftState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.rightState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.states_ruleRelated .counter 0

theorem active_tables_related : FiberTableRelated values leftFiber rightFiber :=
  activeFiberTables_related
    Cordis.GlobalRuleInvariance.HeterogeneousExample.leftState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.rightState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.states_ruleRelated leftPresent rightPresent
    controls (by simp [leftFiber, Cordis.GlobalRegistry.Example.activeProviderFiber,
      Fiber.Active, Phase.Active])

theorem right_target :
    targetView rightState 0 rightFiber =
      some Cordis.GlobalRegistry.Example.emptyProviderView := by
  exact (targetView_some_iff
    Cordis.GlobalRuleInvariance.HeterogeneousExample.leftState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.rightState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.states_ruleRelated leftPresent rightPresent
    controls Cordis.GlobalRegistry.Example.emptyProviderView).1
      Cordis.GlobalRegistry.Example.activeState_target

theorem right_quiescent : Quiescent rightState :=
  (quiescent_iff
    Cordis.GlobalRuleInvariance.HeterogeneousExample.leftState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.rightState_wellFormed
    Cordis.GlobalRuleInvariance.HeterogeneousExample.states_ruleRelated).1
      Cordis.GlobalRegistry.Example.activeState_quiescent

theorem exact_activeContexts_differ : activeContext leftState ≠ activeContext rightState := by
  intro equal
  have atCounter := congrArg (fun context ↦ context .counter) equal
  rw [Cordis.GlobalRegistry.Example.active_counter_exact,
    Cordis.GlobalRuleInvariance.HeterogeneousExample.right_counter_exact] at atCounter
  have impossible : 7 = 9 := Option.some.inj atCounter
  omega

theorem not_effectRelated : ¬EffectRelated leftState rightState := by
  intro related
  have atCounter := related.2 0 .counter
  change some 7 = some 9 at atCounter
  have impossible : 7 = 9 := Option.some.inj atCounter
  omega

/-- Rule observation relates unequal active values and is therefore not effect observation. -/
theorem ruleRelated_without_effectRelated :
    RuleRelated values leftState rightState ∧ ¬EffectRelated leftState rightState :=
  ⟨Cordis.GlobalRuleInvariance.HeterogeneousExample.states_ruleRelated, not_effectRelated⟩

end HeterogeneousExample

namespace EffectObservationGap

/-- Effect observation can identify states with different rule-visible registry domains. -/
theorem effectRelated_without_ruleRelated :
    EffectRelated GlobalRelations.Example.emptyState GlobalRelations.Example.vestigialState ∧
      ¬RuleRelated GlobalRelations.Example.universalValues
        GlobalRelations.Example.emptyState GlobalRelations.Example.vestigialState :=
  ⟨GlobalRelations.Example.effect_related_vestigial_absence,
    GlobalRelations.Example.rule_rejects_vestigial_absence⟩

end EffectObservationGap

/-!
## Ambient boundary
-/

namespace AmbientGap

abbrev baseline := Cordis.GlobalRuleInvariance.InertiaGap.baseline
abbrev shifted := Cordis.GlobalRuleInvariance.InertiaGap.shifted

theorem ambient_values_differ : baseline.ambient ≠ shifted.ambient := by
  simp [baseline, shifted, Cordis.GlobalRuleInvariance.InertiaGap.baseline,
    Cordis.GlobalRuleInvariance.InertiaGap.shifted, Cordis.GlobalDynamics.Example.start]

theorem not_effectRelated : ¬EffectRelated baseline shifted := by
  intro related
  exact ambient_values_differ related.1

/-- Rule observation intentionally forgets ambient state. -/
theorem ruleRelated_without_ambient_equality :
    RuleRelated HeterogeneousExample.values baseline shifted ∧
      baseline.ambient ≠ shifted.ambient :=
  ⟨Cordis.GlobalRuleInvariance.InertiaGap.baseline_ruleRelated_shifted,
    ambient_values_differ⟩

theorem ruleRelated_without_effectRelated :
    RuleRelated HeterogeneousExample.values baseline shifted ∧
      ¬EffectRelated baseline shifted :=
  ⟨Cordis.GlobalRuleInvariance.InertiaGap.baseline_ruleRelated_shifted, not_effectRelated⟩

end AmbientGap

end Cordis.GlobalRuleObservations
