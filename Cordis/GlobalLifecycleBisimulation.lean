import Cordis.GlobalRuleObservations

/-!
# Conditional lifecycle and unified rule bisimulation

This module proves a well-formed finite analogue of CORDIS paper Lemma 55, conditional on four
explicit compatibility surfaces for external dynamics. The assumptions are noncircular: none
mentions `GlobalLifecycle.Transition`, `GlobalCalculus.Step`, either match certificate below, or
any rule-bisimulation structure.

The structural rule observations come from `GlobalRuleObservations`. Iterator landing, exact run
errors, abortability, and accumulated recovery are supplied separately. L-Finish retains its
essential table seam: related reloading sources do not expose owner tables, so a completed pair
of landings must explicitly relate the tables that become active.

The resulting theorem is conditional. It is not paper Lemma 55 derived from the base `Dynamics`
record alone, and it does not inhabit the existing raw, no-`WellFormed` `RuleBisimulation` API.
-/

set_option autoImplicit false

namespace Cordis.GlobalLifecycleBisimulation

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
  Cordis.GlobalCalculus Cordis.GlobalRelations Cordis.GlobalRuleInvariance
  Cordis.GlobalRuleObservations Cordis.GlobalVestigial

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-!
## Noncircular external compatibility certificates
-/

structure LandingMatch
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient)
    {source peer : State catalog Ambient} {owner : sig.Name} {code : sig.IteratorCode}
    {sourceFiber peerFiber : Fiber catalog}
    (landing : Landing dynamics owner code source sourceFiber) where
  peerLanding : Landing dynamics owner code peer peerFiber
  undo_eq : landing.step.undo = peerLanding.step.undo
  next_eq : landing.step.next = peerLanding.step.next
  endpoints_related : RuleRelated values landing.step.after peerLanding.step.after
  tables_if_done : landing.step.next = none →
    FiberTableRelated values landing.afterFiber peerLanding.afterFiber

/-- Bidirectional landing compatibility, stated entirely below the lifecycle relation. -/
structure LandingTransport
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient) where
  forward : ∀ {left right : State catalog Ambient} {owner : sig.Name}
      {code : sig.IteratorCode} {leftFiber rightFiber : Fiber catalog},
    WellFormed left → WellFormed right → RuleRelated values left right →
    right.registry owner = some rightFiber →
    fiberControl leftFiber = fiberControl rightFiber →
    (landing : Landing dynamics owner code left leftFiber) →
      LandingMatch values dynamics (peer := right) (peerFiber := rightFiber) landing
  backward : ∀ {left right : State catalog Ambient} {owner : sig.Name}
      {code : sig.IteratorCode} {leftFiber rightFiber : Fiber catalog},
    WellFormed left → WellFormed right → RuleRelated values left right →
    left.registry owner = some leftFiber →
    fiberControl rightFiber = fiberControl leftFiber →
    (landing : Landing dynamics owner code right rightFiber) →
      LandingMatch values dynamics (peer := left) (peerFiber := leftFiber) landing

/-- Exact raw iterator-error transport; registration-oracle errors are deliberately separate. -/
structure RunErrorTransport
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient) where
  forward : ∀ owner code error {left right : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    dynamics.runIterator owner code left = .error error →
      dynamics.runIterator owner code right = .error error
  backward : ∀ owner code error {left right : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    dynamics.runIterator owner code right = .error error →
      dynamics.runIterator owner code left = .error error

structure RecoveryAdmissionMatch
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient)
    {source peer : State catalog Ambient} {owner : sig.Name}
    {sourceFiber peerFiber : Fiber catalog} {undos : List (UndoCode sig)}
    {outcome : Option sig.Error}
    (admission : RecoveryAdmission dynamics source owner sourceFiber undos outcome) where
  peerAdmission : RecoveryAdmission dynamics peer owner peerFiber undos outcome
  endpoints_related : RuleRelated values admission.after peerAdmission.after

/-- Bidirectional accumulated-recovery compatibility, without mentioning L-Unload. -/
structure RecoveryAdmissionTransport
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient) where
  forward : ∀ {left right : State catalog Ambient} {owner : sig.Name}
      {leftFiber rightFiber : Fiber catalog} {undos : List (UndoCode sig)}
      {outcome : Option sig.Error},
    WellFormed left → WellFormed right → RuleRelated values left right →
    right.registry owner = some rightFiber →
    fiberControl leftFiber = fiberControl rightFiber →
    (admission : RecoveryAdmission dynamics left owner leftFiber undos outcome) →
      RecoveryAdmissionMatch values dynamics (peer := right) (peerFiber := rightFiber) admission
  backward : ∀ {left right : State catalog Ambient} {owner : sig.Name}
      {leftFiber rightFiber : Fiber catalog} {undos : List (UndoCode sig)}
      {outcome : Option sig.Error},
    WellFormed left → WellFormed right → RuleRelated values left right →
    left.registry owner = some leftFiber →
    fiberControl rightFiber = fiberControl leftFiber →
    (admission : RecoveryAdmission dynamics right owner rightFiber undos outcome) →
      RecoveryAdmissionMatch values dynamics (peer := left) (peerFiber := leftFiber) admission

/-- Every nonstructural law needed by the conditional lifecycle theorem. -/
structure LifecycleTransportAssumptions
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  landings : LandingTransport values dynamics
  runErrors : RunErrorTransport values dynamics
  inertia_respects : InertiaRespectsRuleRelated values dynamics inertia
  recovery : RecoveryAdmissionTransport values dynamics

/-!
## Paired phase-update infrastructure
-/

def controlWithPhase
    (control : FiberControl catalog)
    (phase : Phase (catalog.declaration control.component)) : FiberControl catalog :=
  { control with phase := phase }

theorem controlWithPhase_eq
    {left right : FiberControl catalog} (controls : left = right)
    (leftPhase : Phase (catalog.declaration left.component))
    (rightPhase : Phase (catalog.declaration right.component))
    (phaseEq : congrArg FiberControl.component controls ▸ leftPhase = rightPhase) :
    controlWithPhase left leftPhase = controlWithPhase right rightPhase := by
  cases controls
  subst rightPhase
  rfl

theorem fiberControl_setPhase_eq
    {left right : Fiber catalog}
    (controls : fiberControl left = fiberControl right)
    (leftPhase : Phase (catalog.declaration left.component))
    (rightPhase : Phase (catalog.declaration right.component))
    (phaseEq : fiberControl_component_eq controls ▸ leftPhase = rightPhase) :
    fiberControl { left with phase := leftPhase } =
      fiberControl { right with phase := rightPhase } := by
  have proofEq : fiberControl_component_eq controls =
      congrArg FiberControl.component controls := Subsingleton.elim _ _
  rw [proofEq] at phaseEq
  exact controlWithPhase_eq controls leftPhase rightPhase phaseEq

theorem controlAt_setPhase_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPhase : Phase (catalog.declaration leftFiber.component))
    (rightPhase : Phase (catalog.declaration rightFiber.component))
    (updatedControls : fiberControl { leftFiber with phase := leftPhase } =
      fiberControl { rightFiber with phase := rightPhase }) :
    ∀ observed,
      controlAt (setPhase left name leftFiber leftPhase) observed =
        controlAt (setPhase right name rightFiber rightPhase) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    simpa [GlobalRelations.controlAt] using congrArg some updatedControls
  · simpa [GlobalRelations.controlAt, setPhase_lookup_other, same] using
      related.2.2 observed

theorem activeValue_setPhase_iff_of_table_none
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber)
    (next : Phase (catalog.declaration fiber.component))
    {key : sig.Key} (tableNone : fiber.table key = none) {value : sig.Value key} :
    ActiveValue (setPhase state name fiber next) key value ↔ ActiveValue state key value := by
  constructor
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [setPhase_lookup_same] at lookup
      have equal := Option.some.inj lookup
      subst current
      simp [tableNone] at valueEq
    · exact ⟨provider, current,
        by simpa [setPhase_lookup_other, same] using lookup, active, valueEq⟩
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [present] at lookup
      have equal := Option.some.inj lookup
      subst current
      simp [tableNone] at valueEq
    · exact ⟨provider, current,
        by simpa [setPhase_lookup_other, same] using lookup, active, valueEq⟩

theorem activeContext_lookup_eq_of_activeValue_iff
    {left right : State catalog Ambient} (leftWf : WellFormed left)
    (rightWf : WellFormed right) (key : sig.Key)
    (activeValues : ∀ value, ActiveValue left key value ↔ ActiveValue right key value) :
    activeContext left key = activeContext right key := by
  cases leftLookup : activeContext left key with
  | none =>
      cases rightLookup : activeContext right key with
      | none => rfl
      | some rightValue =>
          have rightActive := (activeContext_value_iff rightWf).1 rightLookup
          have leftActive := (activeValues rightValue).2 rightActive
          have impossible := (activeContext_value_iff leftWf).2 leftActive
          rw [leftLookup] at impossible
          cases impossible
  | some leftValue =>
      have leftActive := (activeContext_value_iff leftWf).1 leftLookup
      have rightActive := (activeValues leftValue).1 leftActive
      exact ((activeContext_value_iff rightWf).2 rightActive).symm

theorem activeContext_setPhase_eq_at_of_table_none
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber)
    (next : Phase (catalog.declaration fiber.component))
    (beforeWf : WellFormed state) (afterWf : WellFormed (setPhase state name fiber next))
    (key : sig.Key) (tableNone : fiber.table key = none) :
    activeContext (setPhase state name fiber next) key = activeContext state key := by
  apply activeContext_lookup_eq_of_activeValue_iff afterWf beforeWf key
  intro value
  exact activeValue_setPhase_iff_of_table_none state name fiber present next tableNone

theorem activeContext_setPhase_none_of_table_some_notActive
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (next : Phase (catalog.declaration fiber.component))
    (afterWf : WellFormed (setPhase state name fiber next))
    (nextNotActive : ¬next.Active) {key : sig.Key} {value : sig.Value key}
    (tableSome : fiber.table key = some value) :
    activeContext (setPhase state name fiber next) key = none := by
  cases contextEq : activeContext (setPhase state name fiber next) key with
  | none => rfl
  | some currentValue =>
      obtain ⟨provider, providerFiber, providerPresent, providerActive, providerValue⟩ :=
        (activeContext_value_iff afterWf).1 contextEq
      have ownerPresent := setPhase_lookup_same state name fiber next
      have ownerDeclared := fiber.table_within_provision key (by simp [tableSome])
      have providerDeclared := providerFiber.table_within_provision key (by simp [providerValue])
      have providerEq := afterWf.provisions_unique provider providerFiber name
        { fiber with phase := next } key providerPresent ownerPresent providerDeclared
        ownerDeclared
      subst provider
      rw [ownerPresent] at providerPresent
      have fiberEq := Option.some.inj providerPresent
      subst providerFiber
      exact False.elim (nextNotActive providerActive)

theorem activeContext_setPhase_some_of_table_some_active
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (next : Phase (catalog.declaration fiber.component))
    (afterWf : WellFormed (setPhase state name fiber next))
    (nextActive : next.Active) {key : sig.Key} {value : sig.Value key}
    (tableSome : fiber.table key = some value) :
    activeContext (setPhase state name fiber next) key = some value := by
  apply (activeContext_value_iff afterWf).2
  exact ⟨name, { fiber with phase := next }, setPhase_lookup_same state name fiber next,
    nextActive, tableSome⟩

theorem activeValue_setPhase_iff_of_notActive
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber)
    (next : Phase (catalog.declaration fiber.component))
    (beforeNotActive : ¬fiber.Active) (afterNotActive : ¬next.Active)
    {key : sig.Key} {value : sig.Value key} :
    ActiveValue (setPhase state name fiber next) key value ↔ ActiveValue state key value := by
  constructor
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [setPhase_lookup_same] at lookup
      have equal := Option.some.inj lookup
      subst current
      exact False.elim (afterNotActive active)
    · exact ⟨provider, current,
        by simpa [setPhase_lookup_other, same] using lookup, active, valueEq⟩
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [present] at lookup
      have equal := Option.some.inj lookup
      subst current
      exact False.elim (beforeNotActive active)
    · exact ⟨provider, current,
        by simpa [setPhase_lookup_other, same] using lookup, active, valueEq⟩

theorem activeContext_setPhase_eq_of_notActive
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber)
    (next : Phase (catalog.declaration fiber.component))
    (beforeNotActive : ¬fiber.Active) (afterNotActive : ¬next.Active)
    (beforeWf : WellFormed state) (afterWf : WellFormed (setPhase state name fiber next)) :
    activeContext (setPhase state name fiber next) = activeContext state := by
  apply activeContext_eq_of_activeValue_iff afterWf beforeWf
  intro key value
  exact activeValue_setPhase_iff_of_notActive state name fiber present next beforeNotActive
    afterNotActive

theorem contextRelated_setPhase_nonactive
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (leftBeforeNotActive : ¬leftFiber.Active)
    (rightBeforeNotActive : ¬rightFiber.Active)
    (leftAfterNotActive : ¬leftNext.Active)
    (rightAfterNotActive : ¬rightNext.Active)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    ContextRelated values (activeContext (setPhase left name leftFiber leftNext))
      (activeContext (setPhase right name rightFiber rightNext)) := by
  rw [activeContext_setPhase_eq_of_notActive left name leftFiber leftPresent leftNext
      leftBeforeNotActive leftAfterNotActive leftWf leftAfterWf,
    activeContext_setPhase_eq_of_notActive right name rightFiber rightPresent rightNext
      rightBeforeNotActive rightAfterNotActive rightWf rightAfterWf]
  exact related.1

theorem contextRelated_setPhase_activate
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (leftActive : leftNext.Active) (rightActive : rightNext.Active)
    (tables : FiberTableRelated values leftFiber rightFiber)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    ContextRelated values (activeContext (setPhase left name leftFiber leftNext))
      (activeContext (setPhase right name rightFiber rightNext)) := by
  intro key
  have tableRelated := tables key
  cases leftTableEq : leftFiber.table key with
  | none =>
      cases rightTableEq : rightFiber.table key with
      | none =>
          rw [activeContext_setPhase_eq_at_of_table_none left name leftFiber leftPresent
              leftNext leftWf leftAfterWf key leftTableEq,
            activeContext_setPhase_eq_at_of_table_none right name rightFiber rightPresent
              rightNext rightWf rightAfterWf key rightTableEq]
          exact related.1 key
      | some rightValue => simp [OptionRelated, leftTableEq, rightTableEq] at tableRelated
  | some leftValue =>
      cases rightTableEq : rightFiber.table key with
      | none => simp [OptionRelated, leftTableEq, rightTableEq] at tableRelated
      | some rightValue =>
          rw [activeContext_setPhase_some_of_table_some_active left name leftFiber leftNext
              leftAfterWf leftActive leftTableEq,
            activeContext_setPhase_some_of_table_some_active right name rightFiber rightNext
              rightAfterWf rightActive rightTableEq]
          simpa [OptionRelated, leftTableEq, rightTableEq] using tableRelated

theorem contextRelated_setPhase_deactivate
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (leftNotActive : ¬leftNext.Active) (rightNotActive : ¬rightNext.Active)
    (tables : FiberTableRelated values leftFiber rightFiber)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    ContextRelated values (activeContext (setPhase left name leftFiber leftNext))
      (activeContext (setPhase right name rightFiber rightNext)) := by
  intro key
  have tableRelated := tables key
  cases leftTableEq : leftFiber.table key with
  | none =>
      cases rightTableEq : rightFiber.table key with
      | none =>
          rw [activeContext_setPhase_eq_at_of_table_none left name leftFiber leftPresent
              leftNext leftWf leftAfterWf key leftTableEq,
            activeContext_setPhase_eq_at_of_table_none right name rightFiber rightPresent
              rightNext rightWf rightAfterWf key rightTableEq]
          exact related.1 key
      | some rightValue => simp [OptionRelated, leftTableEq, rightTableEq] at tableRelated
  | some leftValue =>
      cases rightTableEq : rightFiber.table key with
      | none => simp [OptionRelated, leftTableEq, rightTableEq] at tableRelated
      | some rightValue =>
          rw [activeContext_setPhase_none_of_table_some_notActive left name leftFiber leftNext
              leftAfterWf leftNotActive leftTableEq,
            activeContext_setPhase_none_of_table_some_notActive right name rightFiber rightNext
              rightAfterWf rightNotActive rightTableEq]
          trivial

theorem ruleRelated_setPhase
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (updatedControls : fiberControl { leftFiber with phase := leftNext } =
      fiberControl { rightFiber with phase := rightNext })
    (contexts : ContextRelated values
      (activeContext (setPhase left name leftFiber leftNext))
      (activeContext (setPhase right name rightFiber rightNext))) :
    RuleRelated values (setPhase left name leftFiber leftNext)
      (setPhase right name rightFiber rightNext) := by
  exact ⟨contexts, related.2.1,
    controlAt_setPhase_related related name leftFiber rightFiber leftNext rightNext
      updatedControls⟩

/-!
## Dependent phase and landing coherence
-/

theorem phaseInactive_transport
    {left right : sig.ComponentId} (componentEq : left = right)
    (outcome : Option sig.Error) :
    componentEq ▸ Phase.inactive (decl := catalog.declaration left) outcome =
      Phase.inactive (decl := catalog.declaration right) outcome := by
  cases componentEq
  rfl

theorem phaseReloading_transport
    {left right : sig.ComponentId} (componentEq : left = right)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) :
    componentEq ▸ Phase.reloading code undos committed =
      Phase.reloading code undos (transportCommitted componentEq committed) := by
  cases componentEq
  rfl

theorem phaseActive_transport
    {left right : sig.ComponentId} (componentEq : left = right)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) :
    componentEq ▸ Phase.active undos committed =
      Phase.active undos (transportCommitted componentEq committed) := by
  cases componentEq
  rfl

theorem phaseUnloading_transport
    {left right : sig.ComponentId} (componentEq : left = right)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration left)) (outcome : Option sig.Error) :
    componentEq ▸ Phase.unloading undos committed outcome =
      Phase.unloading undos (transportCommitted componentEq committed) outcome := by
  cases componentEq
  rfl

theorem transportCommitted_comp
    {first second third : sig.ComponentId} (leftEq : first = second)
    (rightEq : second = third)
    (committed : CommittedView (catalog.declaration first)) :
    transportCommitted rightEq (transportCommitted leftEq committed) =
      transportCommitted (leftEq.trans rightEq) committed := by
  cases leftEq
  cases rightEq
  rfl

theorem landingCommitted_coherence
    {leftBefore rightBefore leftAfter rightAfter : Fiber catalog}
    (sourceControls : fiberControl leftBefore = fiberControl rightBefore)
    (afterControls : fiberControl leftAfter = fiberControl rightAfter)
    (leftComponent : leftAfter.component = leftBefore.component)
    (rightComponent : rightAfter.component = rightBefore.component)
    (committed : CommittedView (catalog.declaration leftBefore.component)) :
    transportCommitted (fiberControl_component_eq afterControls)
        (transportCommitted leftComponent.symm committed) =
      transportCommitted rightComponent.symm
        (transportCommitted (fiberControl_component_eq sourceControls) committed) := by
  rw [transportCommitted_comp, transportCommitted_comp]

theorem landing_after_controls
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {source peer : State catalog Ambient} {owner : sig.Name} {code : sig.IteratorCode}
    {sourceFiber peerFiber : Fiber catalog}
    {landing : Landing dynamics owner code source sourceFiber}
    (matched : LandingMatch values dynamics (peer := peer) (peerFiber := peerFiber) landing) :
    fiberControl landing.afterFiber = fiberControl matched.peerLanding.afterFiber := by
  let aligned := matchFiber matched.endpoints_related landing.after_present
  have peerPresent := aligned.peer_present
  rw [matched.peerLanding.after_present] at peerPresent
  have fiberEq := Option.some.inj peerPresent
  exact aligned.control_eq.trans (congrArg fiberControl fiberEq.symm)

theorem phaseActive_transport_iff
    {left right : sig.ComponentId} (componentEq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phaseEq : componentEq ▸ leftPhase = rightPhase) :
    leftPhase.Active ↔ rightPhase.Active := by
  cases componentEq
  subst rightPhase
  rfl

theorem landing_after_active_iff
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    landing.afterFiber.Active ↔ beforeFiber.Active := by
  exact phaseActive_transport_iff landing.component_eq landing.afterFiber.phase
    beforeFiber.phase landing.phase_eq

theorem ruleRelated_setPhase_nonactive
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (phaseEq : fiberControl_component_eq controls ▸ leftNext = rightNext)
    (leftBeforeNotActive : ¬leftFiber.Active)
    (rightBeforeNotActive : ¬rightFiber.Active)
    (leftAfterNotActive : ¬leftNext.Active)
    (rightAfterNotActive : ¬rightNext.Active)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    RuleRelated values (setPhase left name leftFiber leftNext)
      (setPhase right name rightFiber rightNext) := by
  apply ruleRelated_setPhase related name leftFiber rightFiber leftNext rightNext
    (fiberControl_setPhase_eq controls leftNext rightNext phaseEq)
  exact contextRelated_setPhase_nonactive leftWf rightWf related name leftFiber rightFiber
    leftPresent rightPresent leftNext rightNext leftBeforeNotActive rightBeforeNotActive
    leftAfterNotActive rightAfterNotActive leftAfterWf rightAfterWf

theorem ruleRelated_setPhase_activate
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (phaseEq : fiberControl_component_eq controls ▸ leftNext = rightNext)
    (leftActive : leftNext.Active) (rightActive : rightNext.Active)
    (tables : FiberTableRelated values leftFiber rightFiber)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    RuleRelated values (setPhase left name leftFiber leftNext)
      (setPhase right name rightFiber rightNext) := by
  apply ruleRelated_setPhase related name leftFiber rightFiber leftNext rightNext
    (fiberControl_setPhase_eq controls leftNext rightNext phaseEq)
  exact contextRelated_setPhase_activate leftWf rightWf related name leftFiber rightFiber
    leftPresent rightPresent leftNext rightNext leftActive rightActive tables leftAfterWf
    rightAfterWf

theorem ruleRelated_setPhase_deactivate
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (leftPresent : left.registry name = some leftFiber)
    (rightPresent : right.registry name = some rightFiber)
    (controls : fiberControl leftFiber = fiberControl rightFiber)
    (leftNext : Phase (catalog.declaration leftFiber.component))
    (rightNext : Phase (catalog.declaration rightFiber.component))
    (phaseEq : fiberControl_component_eq controls ▸ leftNext = rightNext)
    (leftNotActive : ¬leftNext.Active) (rightNotActive : ¬rightNext.Active)
    (tables : FiberTableRelated values leftFiber rightFiber)
    (leftAfterWf : WellFormed (setPhase left name leftFiber leftNext))
    (rightAfterWf : WellFormed (setPhase right name rightFiber rightNext)) :
    RuleRelated values (setPhase left name leftFiber leftNext)
      (setPhase right name rightFiber rightNext) := by
  apply ruleRelated_setPhase related name leftFiber rightFiber leftNext rightNext
    (fiberControl_setPhase_eq controls leftNext rightNext phaseEq)
  exact contextRelated_setPhase_deactivate leftWf rightWf related name leftFiber rightFiber
    leftPresent rightPresent leftNext rightNext leftNotActive rightNotActive tables leftAfterWf
    rightAfterWf

/-!
## Exact lifecycle match certificates
-/

def lifecycleOwner
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Transition dynamics inertia before after → sig.Name
  | .begin _ owner .. => owner
  | .iter _ owner .. => owner
  | .finish _ owner .. => owner
  | .divertAbort _ owner .. => owner
  | .divertLand _ owner .. => owner
  | .raise _ owner .. => owner
  | .leave _ owner .. => owner
  | .unload _ owner .. => owner

structure ForwardLifecycleMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    (transition : Transition dynamics inertia left leftAfter) where
  rightAfter : State catalog Ambient
  matched : Transition dynamics inertia right rightAfter
  same_rule : matched.rule = transition.rule
  same_owner : lifecycleOwner matched = lifecycleOwner transition
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

structure BackwardLifecycleMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    (transition : Transition dynamics inertia right rightAfter) where
  leftAfter : State catalog Ambient
  matched : Transition dynamics inertia left leftAfter
  same_rule : matched.rule = transition.rule
  same_owner : lifecycleOwner matched = lifecycleOwner transition
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

def matchBeginForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (entry : leftFiber.phase = .inactive none)
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (target : targetView left owner leftFiber = some committed) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.begin (dynamics := dynamics) (inertia := inertia) left owner leftFiber
        leftPresent entry committed target) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : BeginGuard left owner leftFiber := {
    present := leftPresent
    committed := committed
    entry := entry
    target := target
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  let leftNext : Phase (catalog.declaration leftFiber.component) :=
    .reloading (catalog.declaration leftFiber.component).entry [] committed
  let rightNext : Phase (catalog.declaration aligned.peerFiber.component) :=
    .reloading (catalog.declaration aligned.peerFiber.component).entry [] rightGuard.committed
  let matched : Transition dynamics inertia right
      (setPhase right owner aligned.peerFiber rightNext) :=
    .begin right owner aligned.peerFiber aligned.peer_present rightGuard.entry
      rightGuard.committed rightGuard.target
  have leftAfterWf :=
    (Transition.begin (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent entry committed target).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have componentEq := fiberControl_component_eq aligned.control_eq
  have entryEq : (catalog.declaration leftFiber.component).entry =
      (catalog.declaration aligned.peerFiber.component).entry :=
    congrArg (fun component ↦ (catalog.declaration component).entry) componentEq
  have nextPhaseEq : componentEq ▸ leftNext = rightNext := by
    rw [show rightNext =
        Phase.reloading (catalog.declaration aligned.peerFiber.component).entry []
          (transportCommitted componentEq committed) by rfl]
    rw [← entryEq]
    exact phaseReloading_transport componentEq _ _ committed
  have leftBeforeNotActive : ¬leftFiber.Active := by
    rw [Fiber.Active, entry]
    simp [Phase.Active]
  have rightBeforeNotActive : ¬aligned.peerFiber.Active := by
    intro active
    exact leftBeforeNotActive ((fiberControl_active_iff aligned.control_eq).2 active)
  have successors := ruleRelated_setPhase_nonactive leftWf rightWf related owner leftFiber
    aligned.peerFiber leftPresent aligned.peer_present aligned.control_eq leftNext rightNext
    nextPhaseEq leftBeforeNotActive rightBeforeNotActive
    (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase right owner aligned.peerFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchDivertAbortForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .reloading code undos committed)
    (targetChanged : targetView left owner leftFiber ≠ some committed)
    (abortable : inertia.canAbort owner code left) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.divertAbort left owner leftFiber leftPresent code undos committed phase
        targetChanged abortable) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : DivertGuard left owner leftFiber := {
    present := leftPresent
    code := code
    undos := undos
    committed := committed
    phase := phase
    target_changed := targetChanged
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  have rightAbortable : inertia.canAbort owner code right :=
    (assumptions.inertia_respects owner code related).1 abortable
  let leftNext : Phase (catalog.declaration leftFiber.component) :=
    .unloading undos committed none
  let rightNext : Phase (catalog.declaration aligned.peerFiber.component) :=
    .unloading undos rightGuard.committed none
  let matched : Transition dynamics inertia right
      (setPhase right owner aligned.peerFiber rightNext) :=
    .divertAbort right owner aligned.peerFiber aligned.peer_present code undos
      rightGuard.committed rightGuard.phase rightGuard.target_changed rightAbortable
  have leftAfterWf :=
    (Transition.divertAbort left owner leftFiber leftPresent code undos committed phase
      targetChanged abortable).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have componentEq := fiberControl_component_eq aligned.control_eq
  have nextPhaseEq : componentEq ▸ leftNext = rightNext := by
    rw [show rightNext = .unloading undos (transportCommitted componentEq committed) none by
      rfl]
    exact phaseUnloading_transport componentEq undos committed none
  have leftBeforeNotActive : ¬leftFiber.Active := by
    rw [Fiber.Active, phase]
    simp [Phase.Active]
  have rightBeforeNotActive : ¬aligned.peerFiber.Active := by
    intro active
    exact leftBeforeNotActive ((fiberControl_active_iff aligned.control_eq).2 active)
  have successors := ruleRelated_setPhase_nonactive leftWf rightWf related owner leftFiber
    aligned.peerFiber leftPresent aligned.peer_present aligned.control_eq leftNext rightNext
    nextPhaseEq leftBeforeNotActive rightBeforeNotActive
    (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase right owner aligned.peerFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchRaiseForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .reloading code undos committed)
    (error : sig.Error) (raised : dynamics.runIterator owner code left = .error error) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.raise left owner leftFiber leftPresent code undos committed phase error
        raised) := by
  let aligned := matchFiber related leftPresent
  let rightCommitted :=
    transportCommitted (fiberControl_component_eq aligned.control_eq) committed
  have rightPhase : aligned.peerFiber.phase = .reloading code undos rightCommitted :=
    (fiberControl_reloading_iff aligned.control_eq code undos committed).1 phase
  have rightRaised : dynamics.runIterator owner code right = .error error :=
    assumptions.runErrors.forward owner code error leftWf rightWf related raised
  let leftNext : Phase (catalog.declaration leftFiber.component) :=
    .unloading undos committed (some error)
  let rightNext : Phase (catalog.declaration aligned.peerFiber.component) :=
    .unloading undos rightCommitted (some error)
  let matched : Transition dynamics inertia right
      (setPhase right owner aligned.peerFiber rightNext) :=
    .raise right owner aligned.peerFiber aligned.peer_present code undos rightCommitted
      rightPhase error rightRaised
  have leftAfterWf :=
    (Transition.raise (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent code undos committed phase error raised).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have componentEq := fiberControl_component_eq aligned.control_eq
  have nextPhaseEq : componentEq ▸ leftNext = rightNext :=
    phaseUnloading_transport componentEq undos committed (some error)
  have leftBeforeNotActive : ¬leftFiber.Active := by
    rw [Fiber.Active, phase]
    simp [Phase.Active]
  have rightBeforeNotActive : ¬aligned.peerFiber.Active := by
    intro active
    exact leftBeforeNotActive ((fiberControl_active_iff aligned.control_eq).2 active)
  have successors := ruleRelated_setPhase_nonactive leftWf rightWf related owner leftFiber
    aligned.peerFiber leftPresent aligned.peer_present aligned.control_eq leftNext rightNext
    nextPhaseEq leftBeforeNotActive rightBeforeNotActive
    (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase right owner aligned.peerFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchLeaveForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics} {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .active undos committed)
    (targetChanged : targetView left owner leftFiber ≠ some committed) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.leave left owner leftFiber leftPresent undos committed phase targetChanged) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : LeaveGuard left owner leftFiber := {
    present := leftPresent
    undos := undos
    committed := committed
    phase := phase
    target_changed := targetChanged
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  let leftNext : Phase (catalog.declaration leftFiber.component) :=
    .unloading undos committed none
  let rightNext : Phase (catalog.declaration aligned.peerFiber.component) :=
    .unloading undos rightGuard.committed none
  let matched : Transition dynamics inertia right
      (setPhase right owner aligned.peerFiber rightNext) :=
    .leave right owner aligned.peerFiber aligned.peer_present undos rightGuard.committed
      rightGuard.phase rightGuard.target_changed
  have leftAfterWf :=
    (Transition.leave (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent undos committed phase targetChanged).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have componentEq := fiberControl_component_eq aligned.control_eq
  have nextPhaseEq : componentEq ▸ leftNext = rightNext := by
    rw [show rightNext = .unloading undos (transportCommitted componentEq committed) none by
      rfl]
    exact phaseUnloading_transport componentEq undos committed none
  have leftActive : leftFiber.Active := by
    rw [Fiber.Active, phase]
    trivial
  have tables := activeFiberTables_related leftWf rightWf related leftPresent
    aligned.peer_present aligned.control_eq leftActive
  have successors := ruleRelated_setPhase_deactivate leftWf rightWf related owner leftFiber
    aligned.peerFiber leftPresent aligned.peer_present aligned.control_eq leftNext rightNext
    nextPhaseEq (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    tables leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase right owner aligned.peerFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchUnloadForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (outcome : Option sig.Error)
    (phase : leftFiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied left owner)
    (admission : RecoveryAdmission dynamics left owner leftFiber undos outcome) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.unload left owner leftFiber leftPresent undos committed outcome phase
        notRelied admission) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : UnloadGuard left owner leftFiber := {
    present := leftPresent
    undos := undos
    committed := committed
    outcome := outcome
    phase := phase
    not_relied := notRelied
  }
  let rightGuard := leftGuard.transport related aligned.peer_present aligned.control_eq
  let recoveryMatch := assumptions.recovery.forward leftWf rightWf related
    aligned.peer_present aligned.control_eq admission
  let matched : Transition dynamics inertia right recoveryMatch.peerAdmission.after :=
    .unload right owner aligned.peerFiber aligned.peer_present undos rightGuard.committed
      outcome rightGuard.phase rightGuard.not_relied recoveryMatch.peerAdmission
  exact {
    rightAfter := recoveryMatch.peerAdmission.after
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := admission.preserves_wellFormed leftWf
    rightAfter_wellFormed := recoveryMatch.peerAdmission.preserves_wellFormed rightWf
    successors_related := recoveryMatch.endpoints_related
  }

def matchIterForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .reloading code undos committed)
    (target : targetView left owner leftFiber = some committed)
    (landing : Landing dynamics owner code left leftFiber)
    (next : sig.IteratorCode) (continues : landing.step.next = some next) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.iter left owner leftFiber leftPresent code undos committed phase target landing
        next continues) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : ReloadingTargetGuard left owner leftFiber := {
    present := leftPresent
    code := code
    undos := undos
    committed := committed
    phase := phase
    target := target
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  let landingMatch := assumptions.landings.forward leftWf rightWf related aligned.peer_present
    aligned.control_eq landing
  have rightContinues : landingMatch.peerLanding.step.next = some next :=
    landingMatch.next_eq.symm.trans continues
  let leftCommitted := transportCommitted landing.component_eq.symm committed
  let rightCommitted :=
    transportCommitted landingMatch.peerLanding.component_eq.symm rightGuard.committed
  let leftNext : Phase (catalog.declaration landing.afterFiber.component) :=
    .reloading next (landing.step.undo :: undos) leftCommitted
  let rightNext : Phase
      (catalog.declaration landingMatch.peerLanding.afterFiber.component) :=
    .reloading next (landingMatch.peerLanding.step.undo :: undos) rightCommitted
  let matched : Transition dynamics inertia right
      (setPhase landingMatch.peerLanding.step.after owner
        landingMatch.peerLanding.afterFiber rightNext) :=
    .iter right owner aligned.peerFiber aligned.peer_present code undos rightGuard.committed
      rightGuard.phase rightGuard.target landingMatch.peerLanding next rightContinues
  have leftBaseWf := landing.step.preservesWellFormed leftWf
  have rightBaseWf := landingMatch.peerLanding.step.preservesWellFormed rightWf
  have leftAfterWf :=
    (Transition.iter (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent code undos committed phase target landing next continues).preservesWellFormed
        leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have afterControls := landing_after_controls landingMatch
  have committedEq : transportCommitted (fiberControl_component_eq afterControls)
      leftCommitted = rightCommitted :=
    landingCommitted_coherence aligned.control_eq afterControls landing.component_eq
      landingMatch.peerLanding.component_eq committed
  have nextPhaseEq : fiberControl_component_eq afterControls ▸ leftNext = rightNext := by
    calc
      fiberControl_component_eq afterControls ▸ leftNext =
          .reloading next (landing.step.undo :: undos)
            (transportCommitted (fiberControl_component_eq afterControls) leftCommitted) :=
        phaseReloading_transport (fiberControl_component_eq afterControls) next
          (landing.step.undo :: undos) leftCommitted
      _ = rightNext := by rw [landingMatch.undo_eq, committedEq]
  have sourceNotActive : ¬leftFiber.Active := by
    rw [Fiber.Active, phase]
    simp [Phase.Active]
  have leftBeforeNotActive : ¬landing.afterFiber.Active := by
    intro active
    exact sourceNotActive ((landing_after_active_iff landing).1 active)
  have rightBeforeNotActive : ¬landingMatch.peerLanding.afterFiber.Active := by
    intro active
    exact leftBeforeNotActive ((fiberControl_active_iff afterControls).2 active)
  have successors := ruleRelated_setPhase_nonactive leftBaseWf rightBaseWf
    landingMatch.endpoints_related owner landing.afterFiber landingMatch.peerLanding.afterFiber
    landing.after_present landingMatch.peerLanding.after_present afterControls leftNext rightNext
    nextPhaseEq leftBeforeNotActive rightBeforeNotActive
    (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase landingMatch.peerLanding.step.after owner
      landingMatch.peerLanding.afterFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchFinishForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .reloading code undos committed)
    (target : targetView left owner leftFiber = some committed)
    (landing : Landing dynamics owner code left leftFiber)
    (done : landing.step.next = none) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.finish left owner leftFiber leftPresent code undos committed phase target
        landing done) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : ReloadingTargetGuard left owner leftFiber := {
    present := leftPresent
    code := code
    undos := undos
    committed := committed
    phase := phase
    target := target
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  let landingMatch := assumptions.landings.forward leftWf rightWf related aligned.peer_present
    aligned.control_eq landing
  have rightDone : landingMatch.peerLanding.step.next = none :=
    landingMatch.next_eq.symm.trans done
  let leftCommitted := transportCommitted landing.component_eq.symm committed
  let rightCommitted :=
    transportCommitted landingMatch.peerLanding.component_eq.symm rightGuard.committed
  let leftNext : Phase (catalog.declaration landing.afterFiber.component) :=
    .active (landing.step.undo :: undos) leftCommitted
  let rightNext : Phase
      (catalog.declaration landingMatch.peerLanding.afterFiber.component) :=
    .active (landingMatch.peerLanding.step.undo :: undos) rightCommitted
  let matched : Transition dynamics inertia right
      (setPhase landingMatch.peerLanding.step.after owner
        landingMatch.peerLanding.afterFiber rightNext) :=
    .finish right owner aligned.peerFiber aligned.peer_present code undos rightGuard.committed
      rightGuard.phase rightGuard.target landingMatch.peerLanding rightDone
  have leftBaseWf := landing.step.preservesWellFormed leftWf
  have rightBaseWf := landingMatch.peerLanding.step.preservesWellFormed rightWf
  have leftAfterWf :=
    (Transition.finish (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent code undos committed phase target landing done).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have afterControls := landing_after_controls landingMatch
  have committedEq : transportCommitted (fiberControl_component_eq afterControls)
      leftCommitted = rightCommitted :=
    landingCommitted_coherence aligned.control_eq afterControls landing.component_eq
      landingMatch.peerLanding.component_eq committed
  have nextPhaseEq : fiberControl_component_eq afterControls ▸ leftNext = rightNext := by
    calc
      fiberControl_component_eq afterControls ▸ leftNext =
          .active (landing.step.undo :: undos)
            (transportCommitted (fiberControl_component_eq afterControls) leftCommitted) :=
        phaseActive_transport (fiberControl_component_eq afterControls)
          (landing.step.undo :: undos) leftCommitted
      _ = rightNext := by rw [landingMatch.undo_eq, committedEq]
  have tables := landingMatch.tables_if_done done
  have successors := ruleRelated_setPhase_activate leftBaseWf rightBaseWf
    landingMatch.endpoints_related owner landing.afterFiber landingMatch.peerLanding.afterFiber
    landing.after_present landingMatch.peerLanding.after_present afterControls leftNext rightNext
    nextPhaseEq (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    tables leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase landingMatch.peerLanding.step.after owner
      landingMatch.peerLanding.afterFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def matchDivertLandForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (owner : sig.Name) (leftFiber : Fiber catalog)
    (leftPresent : left.registry owner = some leftFiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration leftFiber.component))
    (phase : leftFiber.phase = .reloading code undos committed)
    (targetChanged : targetView left owner leftFiber ≠ some committed)
    (landing : Landing dynamics owner code left leftFiber) :
    ForwardLifecycleMatch values (dynamics := dynamics) (inertia := inertia) (right := right)
      (Transition.divertLand left owner leftFiber leftPresent code undos committed phase
        targetChanged landing) := by
  let aligned := matchFiber related leftPresent
  let leftGuard : DivertGuard left owner leftFiber := {
    present := leftPresent
    code := code
    undos := undos
    committed := committed
    phase := phase
    target_changed := targetChanged
  }
  let rightGuard := leftGuard.transport leftWf rightWf related aligned.peer_present
    aligned.control_eq
  let landingMatch := assumptions.landings.forward leftWf rightWf related aligned.peer_present
    aligned.control_eq landing
  let leftCommitted := transportCommitted landing.component_eq.symm committed
  let rightCommitted :=
    transportCommitted landingMatch.peerLanding.component_eq.symm rightGuard.committed
  let leftNext : Phase (catalog.declaration landing.afterFiber.component) :=
    .unloading (landing.step.undo :: undos) leftCommitted none
  let rightNext : Phase
      (catalog.declaration landingMatch.peerLanding.afterFiber.component) :=
    .unloading (landingMatch.peerLanding.step.undo :: undos) rightCommitted none
  let matched : Transition dynamics inertia right
      (setPhase landingMatch.peerLanding.step.after owner
        landingMatch.peerLanding.afterFiber rightNext) :=
    .divertLand right owner aligned.peerFiber aligned.peer_present code undos
      rightGuard.committed rightGuard.phase rightGuard.target_changed landingMatch.peerLanding
  have leftBaseWf := landing.step.preservesWellFormed leftWf
  have rightBaseWf := landingMatch.peerLanding.step.preservesWellFormed rightWf
  have leftAfterWf :=
    (Transition.divertLand (dynamics := dynamics) (inertia := inertia) left owner leftFiber
      leftPresent code undos committed phase targetChanged landing).preservesWellFormed leftWf
  have rightAfterWf := matched.preservesWellFormed rightWf
  have afterControls := landing_after_controls landingMatch
  have committedEq : transportCommitted (fiberControl_component_eq afterControls)
      leftCommitted = rightCommitted :=
    landingCommitted_coherence aligned.control_eq afterControls landing.component_eq
      landingMatch.peerLanding.component_eq committed
  have nextPhaseEq : fiberControl_component_eq afterControls ▸ leftNext = rightNext := by
    calc
      fiberControl_component_eq afterControls ▸ leftNext =
          .unloading (landing.step.undo :: undos)
            (transportCommitted (fiberControl_component_eq afterControls) leftCommitted) none :=
        phaseUnloading_transport (fiberControl_component_eq afterControls)
          (landing.step.undo :: undos) leftCommitted none
      _ = rightNext := by rw [landingMatch.undo_eq, committedEq]
  have sourceNotActive : ¬leftFiber.Active := by
    rw [Fiber.Active, phase]
    simp [Phase.Active]
  have leftBeforeNotActive : ¬landing.afterFiber.Active := by
    intro active
    exact sourceNotActive ((landing_after_active_iff landing).1 active)
  have rightBeforeNotActive : ¬landingMatch.peerLanding.afterFiber.Active := by
    intro active
    exact leftBeforeNotActive ((fiberControl_active_iff afterControls).2 active)
  have successors := ruleRelated_setPhase_nonactive leftBaseWf rightBaseWf
    landingMatch.endpoints_related owner landing.afterFiber landingMatch.peerLanding.afterFiber
    landing.after_present landingMatch.peerLanding.after_present afterControls leftNext rightNext
    nextPhaseEq leftBeforeNotActive rightBeforeNotActive
    (by simp [leftNext, Phase.Active]) (by simp [rightNext, Phase.Active])
    leftAfterWf rightAfterWf
  exact {
    rightAfter := setPhase landingMatch.peerLanding.step.after owner
      landingMatch.peerLanding.afterFiber rightNext
    matched := matched
    same_rule := rfl
    same_owner := rfl
    leftAfter_wellFormed := leftAfterWf
    rightAfter_wellFormed := rightAfterWf
    successors_related := successors
  }

def LandingTransport.symm
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    (transport : LandingTransport values dynamics) : LandingTransport values dynamics where
  forward := by
    intro left right owner code leftFiber rightFiber leftWf rightWf related rightPresent
      controls landing
    exact transport.backward rightWf leftWf (ruleRelated_symm related) rightPresent controls
      landing
  backward := by
    intro left right owner code leftFiber rightFiber leftWf rightWf related leftPresent
      controls landing
    exact transport.forward rightWf leftWf (ruleRelated_symm related) leftPresent controls
      landing

theorem RunErrorTransport.symm
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    (transport : RunErrorTransport values dynamics) : RunErrorTransport values dynamics where
  forward := by
    intro owner code error left right leftWf rightWf related raised
    exact transport.backward owner code error rightWf leftWf (ruleRelated_symm related) raised
  backward := by
    intro owner code error left right leftWf rightWf related raised
    exact transport.forward owner code error rightWf leftWf (ruleRelated_symm related) raised

def RecoveryAdmissionTransport.symm
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    (transport : RecoveryAdmissionTransport values dynamics) :
    RecoveryAdmissionTransport values dynamics where
  forward := by
    intro left right owner leftFiber rightFiber undos outcome leftWf rightWf related
      rightPresent controls admission
    exact transport.backward rightWf leftWf (ruleRelated_symm related) rightPresent controls
      admission
  backward := by
    intro left right owner leftFiber rightFiber undos outcome leftWf rightWf related
      leftPresent controls admission
    exact transport.forward rightWf leftWf (ruleRelated_symm related) leftPresent controls
      admission

def LifecycleTransportAssumptions.symm
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia) :
    LifecycleTransportAssumptions values dynamics inertia where
  landings := assumptions.landings.symm
  runErrors := assumptions.runErrors.symm
  inertia_respects := by
    intro owner code left right related
    exact (assumptions.inertia_respects owner code (ruleRelated_symm related)).symm
  recovery := assumptions.recovery.symm

def matchLifecycleForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right leftAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (transition : Transition dynamics inertia left leftAfter) :
    ForwardLifecycleMatch values (right := right) transition := by
  cases transition with
  | begin owner fiber present entry committed target =>
      exact matchBeginForward leftWf rightWf related owner fiber present entry committed target
  | iter owner fiber present code undos committed phase target landing next continues =>
      exact matchIterForward assumptions leftWf rightWf related owner fiber present code undos
        committed phase target landing next continues
  | finish owner fiber present code undos committed phase target landing done =>
      exact matchFinishForward assumptions leftWf rightWf related owner fiber present code undos
        committed phase target landing done
  | divertAbort owner fiber present code undos committed phase targetChanged abortable =>
      exact matchDivertAbortForward assumptions leftWf rightWf related owner fiber present code
        undos committed phase targetChanged abortable
  | divertLand owner fiber present code undos committed phase targetChanged landing =>
      exact matchDivertLandForward assumptions leftWf rightWf related owner fiber present code
        undos committed phase targetChanged landing
  | raise owner fiber present code undos committed phase error raised =>
      exact matchRaiseForward assumptions leftWf rightWf related owner fiber present code undos
        committed phase error raised
  | leave owner fiber present undos committed phase targetChanged =>
      exact matchLeaveForward leftWf rightWf related owner fiber present undos committed phase
        targetChanged
  | unload owner fiber present undos committed outcome phase notRelied admission =>
      exact matchUnloadForward assumptions leftWf rightWf related owner fiber present undos
        committed outcome phase notRelied admission

def matchLifecycleBackward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right rightAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (transition : Transition dynamics inertia right rightAfter) :
    BackwardLifecycleMatch values (left := left) transition := by
  let swapped := matchLifecycleForward assumptions.symm rightWf leftWf
    (ruleRelated_symm related) transition
  exact {
    leftAfter := swapped.rightAfter
    matched := swapped.matched
    same_rule := swapped.same_rule
    same_owner := swapped.same_owner
    leftAfter_wellFormed := swapped.rightAfter_wellFormed
    rightAfter_wellFormed := swapped.leftAfter_wellFormed
    successors_related := ruleRelated_symm swapped.successors_related
  }

structure LifecycleRuleBisimulation
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (transition : Transition dynamics inertia left leftAfter) →
      ForwardLifecycleMatch values (right := right) transition
  backward : ∀ {left right rightAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (transition : Transition dynamics inertia right rightAfter) →
      BackwardLifecycleMatch values (left := left) transition

def lifecycleRuleBisimulation
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia) :
    LifecycleRuleBisimulation values dynamics inertia where
  forward := matchLifecycleForward assumptions
  backward := matchLifecycleBackward assumptions

/-!
## Unified well-formed ten-name certificate
-/

theorem orchestration_step_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftStep : OrchestrationStep leftBefore leftAfter}
    {rightStep : OrchestrationStep rightBefore rightAfter}
    (same : orchestrationKind rightStep = orchestrationKind leftStep) :
    (Step.orchestration (dynamics := dynamics) (inertia := inertia) rightStep).rule =
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) leftStep).rule := by
  cases leftStep <;> cases rightStep <;> simp [orchestrationKind] at same
  all_goals rfl

theorem orchestration_step_actor_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftStep : OrchestrationStep leftBefore leftAfter}
    {rightStep : OrchestrationStep rightBefore rightAfter}
    (same : orchestrationName rightStep = orchestrationName leftStep) :
    (Step.orchestration (dynamics := dynamics) (inertia := inertia) rightStep).actedName =
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) leftStep).actedName := by
  cases leftStep <;> cases rightStep <;> exact same

theorem lifecycle_step_rule_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftTransition : Transition dynamics inertia leftBefore leftAfter}
    {rightTransition : Transition dynamics inertia rightBefore rightAfter}
    (same : rightTransition.rule = leftTransition.rule) :
    (Step.lifecycle rightTransition).rule = (Step.lifecycle leftTransition).rule := by
  cases leftTransition <;> cases rightTransition <;> simp [Transition.rule] at same
  all_goals rfl

theorem lifecycle_step_actor_eq
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftTransition : Transition dynamics inertia leftBefore leftAfter}
    {rightTransition : Transition dynamics inertia rightBefore rightAfter}
    (same : lifecycleOwner rightTransition = lifecycleOwner leftTransition) :
    (Step.lifecycle rightTransition).actedName = (Step.lifecycle leftTransition).actedName := by
  cases leftTransition <;> cases rightTransition <;> exact same

structure ForwardStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    (step : Step dynamics inertia left leftAfter) where
  rightAfter : State catalog Ambient
  matched : Step dynamics inertia right rightAfter
  same_rule : matched.rule = step.rule
  same_actor : matched.actedName = step.actedName
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

structure BackwardStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    (step : Step dynamics inertia right rightAfter) where
  leftAfter : State catalog Ambient
  matched : Step dynamics inertia left leftAfter
  same_rule : matched.rule = step.rule
  same_actor : matched.actedName = step.actedName
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

def matchStepForward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right leftAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (step : Step dynamics inertia left leftAfter) :
    ForwardStepMatch values (right := right) step := by
  cases step with
  | orchestration orchestrationStep =>
      let result := matchOrchestrationForward leftWf rightWf related orchestrationStep
      exact {
        rightAfter := result.rightAfter
        matched := .orchestration result.matched
        same_rule := orchestration_step_rule_eq result.same_kind
        same_actor := orchestration_step_actor_eq result.same_actor
        leftAfter_wellFormed := result.leftAfter_wellFormed
        rightAfter_wellFormed := result.rightAfter_wellFormed
        successors_related := result.successors_related
      }
  | lifecycle transition =>
      let result := matchLifecycleForward assumptions leftWf rightWf related transition
      exact {
        rightAfter := result.rightAfter
        matched := .lifecycle result.matched
        same_rule := lifecycle_step_rule_eq result.same_rule
        same_actor := lifecycle_step_actor_eq result.same_owner
        leftAfter_wellFormed := result.leftAfter_wellFormed
        rightAfter_wellFormed := result.rightAfter_wellFormed
        successors_related := result.successors_related
      }

def matchStepBackward
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia)
    {left right rightAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (step : Step dynamics inertia right rightAfter) :
    BackwardStepMatch values (left := left) step := by
  let swapped := matchStepForward assumptions.symm rightWf leftWf
    (ruleRelated_symm related) step
  exact {
    leftAfter := swapped.rightAfter
    matched := swapped.matched
    same_rule := swapped.same_rule
    same_actor := swapped.same_actor
    leftAfter_wellFormed := swapped.rightAfter_wellFormed
    rightAfter_wellFormed := swapped.leftAfter_wellFormed
    successors_related := ruleRelated_symm swapped.successors_related
  }

/-- Conditional well-formed analogue of the paper's unified ten-rule Lemma 55 certificate. -/
structure WellFormedRuleBisimulation
    (values : ValueSetoids sig) (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (step : Step dynamics inertia left leftAfter) →
      ForwardStepMatch values (right := right) step
  backward : ∀ {left right rightAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (step : Step dynamics inertia right rightAfter) →
      BackwardStepMatch values (left := left) step

def wellFormedRuleBisimulation
    {values : ValueSetoids sig} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : LifecycleTransportAssumptions values dynamics inertia) :
    WellFormedRuleBisimulation values dynamics inertia where
  forward := matchStepForward assumptions
  backward := matchStepBackward assumptions

/-!
## Pointwise reflexive compatibility

A universal reflexive assumption bundle is intentionally not claimed: its fields quantify over
distinct `RuleRelated` states, and arbitrary dynamics or inertia need not respect that relation.
The diagonal certificates below are assumption-free and exercise exact executable paths.
-/

theorem fiberTableRelated_refl
    (values : ValueSetoids sig) (fiber : Fiber catalog) :
    FiberTableRelated values fiber fiber := by
  intro key
  exact OptionRelated.refl (values.relation key) (fiber.table key)

def LandingMatch.refl
    (values : ValueSetoids sig) {dynamics : Dynamics sig catalog Ambient}
    {owner : sig.Name} {code : sig.IteratorCode} {state : State catalog Ambient}
    {fiber : Fiber catalog} (landing : Landing dynamics owner code state fiber) :
    LandingMatch values dynamics (peer := state) (peerFiber := fiber) landing where
  peerLanding := landing
  undo_eq := rfl
  next_eq := rfl
  endpoints_related := ruleRelated_refl values landing.step.after
  tables_if_done := fun _ ↦ fiberTableRelated_refl values landing.afterFiber

def RecoveryAdmissionMatch.refl
    (values : ValueSetoids sig) {dynamics : Dynamics sig catalog Ambient}
    {state : State catalog Ambient} {owner : sig.Name} {fiber : Fiber catalog}
    {undos : List (UndoCode sig)} {outcome : Option sig.Error}
    (admission : RecoveryAdmission dynamics state owner fiber undos outcome) :
    RecoveryAdmissionMatch values dynamics (peer := state) (peerFiber := fiber) admission where
  peerAdmission := admission
  endpoints_related := ruleRelated_refl values admission.after

def ForwardLifecycleMatch.refl
    (values : ValueSetoids sig) {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics} {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) (wf : WellFormed before) :
    ForwardLifecycleMatch values (right := before) transition where
  rightAfter := after
  matched := transition
  same_rule := rfl
  same_owner := rfl
  leftAfter_wellFormed := transition.preservesWellFormed wf
  rightAfter_wellFormed := transition.preservesWellFormed wf
  successors_related := ruleRelated_refl values after

def ForwardStepMatch.refl
    (values : ValueSetoids sig) {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics} {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (wf : WellFormed before) :
    ForwardStepMatch values (right := before) step where
  rightAfter := after
  matched := step
  same_rule := rfl
  same_actor := rfl
  leftAfter_wellFormed := step.preservesWellFormed wf
  rightAfter_wellFormed := step.preservesWellFormed wf
  successors_related := ruleRelated_refl values after

namespace ReflexiveExample

abbrev values := Cordis.GlobalRuleInvariance.HeterogeneousExample.values

def firstLandingMatch : LandingMatch values Cordis.GlobalLifecycle.Example.dynamics
    (peer := Cordis.GlobalLifecycle.Example.beginState)
    (peerFiber := Cordis.GlobalLifecycle.Example.beginFiber)
    Cordis.GlobalLifecycle.Example.firstLanding :=
  LandingMatch.refl values Cordis.GlobalLifecycle.Example.firstLanding

def finalLandingMatch : LandingMatch values Cordis.GlobalLifecycle.Example.dynamics
    (peer := Cordis.GlobalLifecycle.Example.iterState)
    (peerFiber := Cordis.GlobalLifecycle.Example.iterFiber)
    Cordis.GlobalLifecycle.Example.finalLanding :=
  LandingMatch.refl values Cordis.GlobalLifecycle.Example.finalLanding

def recoveryMatch : RecoveryAdmissionMatch values Cordis.GlobalLifecycle.Example.dynamics
    (peer := Cordis.GlobalLifecycle.Example.leaveState)
    (peerFiber := Cordis.GlobalLifecycle.Example.unloadingFiber)
    Cordis.GlobalLifecycle.Example.recoveryAdmission :=
  RecoveryAdmissionMatch.refl values Cordis.GlobalLifecycle.Example.recoveryAdmission

def beginMatch : ForwardLifecycleMatch values
    (right := Cordis.GlobalLifecycle.Example.start)
    Cordis.GlobalLifecycle.Example.beginTransition :=
  ForwardLifecycleMatch.refl values Cordis.GlobalLifecycle.Example.beginTransition
    Cordis.GlobalLifecycle.Example.start_wellFormed

def iterMatch : ForwardLifecycleMatch values
    (right := Cordis.GlobalLifecycle.Example.beginState)
    Cordis.GlobalLifecycle.Example.iterTransition :=
  ForwardLifecycleMatch.refl values Cordis.GlobalLifecycle.Example.iterTransition
    Cordis.GlobalLifecycle.Example.beginState_wellFormed

def finishMatch : ForwardLifecycleMatch values
    (right := Cordis.GlobalLifecycle.Example.iterState)
    Cordis.GlobalLifecycle.Example.finishTransition :=
  ForwardLifecycleMatch.refl values Cordis.GlobalLifecycle.Example.finishTransition
    Cordis.GlobalLifecycle.Example.iterState_wellFormed

def leaveMatch : ForwardLifecycleMatch values
    (right := Cordis.GlobalLifecycle.Example.retiredState)
    Cordis.GlobalLifecycle.Example.leaveTransition :=
  ForwardLifecycleMatch.refl values Cordis.GlobalLifecycle.Example.leaveTransition
    Cordis.GlobalLifecycle.Example.retiredState_wellFormed

def unloadMatch : ForwardLifecycleMatch values
    (right := Cordis.GlobalLifecycle.Example.leaveState)
    Cordis.GlobalLifecycle.Example.unloadTransition :=
  ForwardLifecycleMatch.refl values Cordis.GlobalLifecycle.Example.unloadTransition
    Cordis.GlobalLifecycle.Example.leaveState_wellFormed

theorem existing_path_rules :
    [beginMatch.matched.rule, iterMatch.matched.rule, finishMatch.matched.rule,
      leaveMatch.matched.rule, unloadMatch.matched.rule] =
    [.begin, .iter, .finish, .leave, .unload] := rfl

end ReflexiveExample

/-!
## Kernel counterexample for the L-Finish table seam
-/

namespace FinishSeam

abbrev Signature := Cordis.GlobalRegistry.Example.signature
abbrev Catalog := Cordis.GlobalRegistry.Example.catalog
abbrev Key := Cordis.GlobalRegistry.Example.Key
abbrev Value := Cordis.GlobalRegistry.Example.Value
abbrev ExampleState := GlobalState Catalog Unit
abbrev values := Cordis.GlobalRuleInvariance.HeterogeneousExample.values

def table (counter : Nat) : Coeffect.Context Key Value :=
  Coeffect.setAt Coeffect.empty .counter (show Value .counter from counter)

def fiber (counter : Nat) : Fiber Catalog where
  component := .provider
  parent := none
  birth := 0
  table := table counter
  table_within_provision := by
    intro key present
    cases key <;> simp [Cordis.GlobalRegistry.Example.providerDecl]
  retired := false
  phase := .reloading 0 [] Cordis.GlobalRegistry.Example.emptyProviderView

def state (counter : Nat) : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty 0 (fiber counter)

theorem present (counter : Nat) : (state counter).registry 0 = some (fiber counter) := rfl

theorem state_wellFormed (counter : Nat) : WellFormed (state counter) := by
  constructor
  · intro name current lookup
    by_cases same : name = 0
    · subst name
      simp [state] at lookup
      subst current
      simp [state, fiber]
    · simp [state, Coeffect.setAt_other, same] at lookup
  · intro name current parent lookup parentEq
    by_cases same : name = 0
    · subst name
      simp [state] at lookup
      subst current
      simp [fiber] at parentEq
    · simp [state, Coeffect.setAt_other, same] at lookup
  · intro name current parent parentFiber lookup parentEq parentLookup
    by_cases same : name = 0
    · subst name
      simp [state] at lookup
      subst current
      simp [fiber] at parentEq
    · simp [state, Coeffect.setAt_other, same] at lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    have leftEq : left = 0 := by
      by_cases same : left = 0
      · exact same
      · simp [state, Coeffect.setAt_other, same] at leftLookup
    have rightEq : right = 0 := by
      by_cases same : right = 0
      · exact same
      · simp [state, Coeffect.setAt_other, same] at rightLookup
    exact leftEq.trans rightEq.symm
  · intro name current lookup committed committedEq declared
    by_cases same : name = 0
    · subst name
      simp [state] at lookup
      subst current
      rcases declared with ⟨key, declared⟩
      change key ∈ Cordis.GlobalRegistry.Example.providerDecl.dependencies.keys at declared
      simp [Cordis.GlobalRegistry.Example.providerDecl] at declared
    · simp [state, Coeffect.setAt_other, same] at lookup
  · intro name current lookup committed committedEq declared providerFiber providerLookup
    by_cases same : name = 0
    · subst name
      simp [state] at lookup
      subst current
      rcases declared with ⟨key, declared⟩
      change key ∈ Cordis.GlobalRegistry.Example.providerDecl.dependencies.keys at declared
      simp [Cordis.GlobalRegistry.Example.providerDecl] at declared
    · simp [state, Coeffect.setAt_other, same] at lookup

theorem activeContext_empty (counter : Nat) :
    activeContext (state counter) = Coeffect.empty := by
  apply Coeffect.Context.ext
  intro key
  cases contextEq : activeContext (state counter) key with
  | none => rfl
  | some value =>
      obtain ⟨name, current, lookup, active, valueEq⟩ :=
        (activeContext_value_iff (state_wellFormed counter)).1 contextEq
      by_cases same : name = 0
      · subst name
        simp [state] at lookup
        subst current
        simp [fiber, Fiber.Active, Phase.Active] at active
      · simp [state, Coeffect.setAt_other, same] at lookup

theorem sources_ruleRelated : RuleRelated values (state 7) (state 8) := by
  constructor
  · rw [activeContext_empty 7, activeContext_empty 8]
    exact contextRelated_refl values Coeffect.empty
  · constructor
    · rfl
    · intro name
      by_cases same : name = 0
      · subst name
        rfl
      · simp [state, GlobalRelations.controlAt, Coeffect.setAt_other, same]

theorem source_tables_not_related : ¬FiberTableRelated values (fiber 7) (fiber 8) := by
  intro related
  have atCounter := related .counter
  change 7 % 2 = 8 % 2 at atCounter
  omega

def activated (counter : Nat) : ExampleState :=
  setPhase (state counter) 0 (fiber counter)
    (.active [] Cordis.GlobalRegistry.Example.emptyProviderView)

theorem activated_wellFormed (counter : Nat) : WellFormed (activated counter) := by
  apply setPhase_installed_preserves (present counter) _ (by simp [Phase.Installed]) _
    (state_wellFormed counter)
  intro committed committedEq declared
  rcases declared with ⟨key, declared⟩
  change key ∈ Cordis.GlobalRegistry.Example.providerDecl.dependencies.keys at declared
  simp [Cordis.GlobalRegistry.Example.providerDecl] at declared

theorem activated_counter_exact (counter : Nat) :
    activeContext (activated counter) .counter = some counter := by
  apply (activeContext_value_iff (activated_wellFormed counter)).2
  exact ⟨0, { fiber counter with
      phase := .active [] Cordis.GlobalRegistry.Example.emptyProviderView }, rfl,
    by simp [Fiber.Active, Phase.Active], rfl⟩

/-- Activating unrelated reloading tables destroys rule observation. -/
theorem activated_not_ruleRelated : ¬RuleRelated values (activated 7) (activated 8) := by
  intro related
  have atCounter := related.1 .counter
  rw [activated_counter_exact 7, activated_counter_exact 8] at atCounter
  change 7 % 2 = 8 % 2 at atCounter
  omega

end FinishSeam

end Cordis.GlobalLifecycleBisimulation
