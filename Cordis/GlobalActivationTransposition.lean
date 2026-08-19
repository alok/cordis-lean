import Cordis.GlobalLandingTransposition
import Cordis.GlobalRuleObservations

/-!
# Fixed-program activation transposition

This module implements the bounded all-nine activation layer specified in
`docs/GLOBAL_ACTIVATION_TRANSPOSITION_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

`ProgramActivation` represents exactly L-Begin, L-Iter, and L-Finish under one fixed program.
The branch-minimal law surface asks for no iterator law in Begin/Begin, only the landing program's
foreign-phase compatibility in a mixed pair, and exact forward lifecycle independence only when
both sides execute iterators. The common-source theorem constructs both actual lifecycle orders;
a second wrapper identifies its normal-order endpoint with a separately supplied actual second
activation using fixed-program endpoint determinism.

This is an exact fixed-oracle refinement with possibly undefined executions, rather than paper
Lemma 71 verbatim. It does
not cover other lifecycle rules, orchestration exchange, episode provenance, trace rewriting,
Theorem 61, Corollary 62, confluence, or progress.
-/

set_option autoImplicit false

namespace Cordis.GlobalActivationTransposition

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalIteratorIndependence Cordis.GlobalTransposition
open Cordis.GlobalForeignPhase Cordis.GlobalLandingTransposition
open Cordis.GlobalRuleObservations

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Complete fixed-program activation -/

/-- One L-Begin, or one already program-aligned L-Iter/L-Finish activation. -/
inductive ProgramActivation
    {dynamics : Dynamics sig catalog Ambient}
    (program : Program dynamics) (before : State catalog Ambient) : Type (u + 1) where
  | begin
      (fiber : Fiber catalog)
      (guard : BeginGuard before program.owner fiber)
      (root_aligned : program.root = (catalog.declaration fiber.component).entry)
  | landing
      (activation : ProgramAlignedLandingActivation program before)

namespace ProgramActivation

/-- Exact endpoint derived from the actual Begin or landing payload. -/
def after
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramActivation program before) : State catalog Ambient :=
  match activation with
  | .begin fiber guard _ =>
      setPhase before program.owner fiber
        (.reloading (catalog.declaration fiber.component).entry [] guard.committed)
  | .landing aligned => aligned.after

/-- Exact lifecycle rule. -/
def rule
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} : ProgramActivation program before → Rule
  | .begin .. => .begin
  | .landing aligned => aligned.rule

/-- Source owner fiber retained by the proof-carrying activation. -/
def sourceFiber
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} : ProgramActivation program before → Fiber catalog
  | .begin fiber .. => fiber
  | .landing aligned => aligned.fiber

/-- Branch index used by the minimal semantic law package. -/
def UsesIterator
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramActivation program before) : Prop :=
  match activation with
  | .begin .. => False
  | .landing .. => True

/-- Every activation converts to an actual lifecycle transition at its derived endpoint. -/
def transition
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramActivation program before)
    (inertia : InertiaPolicy dynamics) : Transition dynamics inertia before activation.after := by
  cases activation with
  | begin fiber guard rootAligned =>
      exact .begin before program.owner fiber guard.present guard.entry guard.committed guard.target
  | landing aligned => exact aligned.transition inertia

@[simp] theorem transition_rule
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramActivation program before) (inertia : InertiaPolicy dynamics) :
    (activation.transition inertia).rule = activation.rule := by
  cases activation with
  | begin => rfl
  | landing aligned => exact aligned.transition_rule inertia

theorem source_present
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (activation : ProgramActivation program before) :
    before.registry program.owner = some activation.sourceFiber := by
  cases activation with
  | begin fiber guard rootAligned => exact guard.present
  | landing aligned => exact aligned.present

theorem source_not_active
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (activation : ProgramActivation program before) :
    ¬activation.sourceFiber.Active := by
  cases activation with
  | begin fiber guard rootAligned =>
      change ¬fiber.Active
      rw [Fiber.Active, guard.entry]
      simp [Phase.Active]
  | landing aligned =>
      change ¬ aligned.fiber.Active
      rw [Fiber.Active, aligned.phase]
      simp [Phase.Active]

theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (activation : ProgramActivation program before)
    (inertia : InertiaPolicy dynamics) : WellFormed before → WellFormed activation.after :=
  (activation.transition inertia).preservesWellFormed

end ProgramActivation

/-! ## Exact foreign lookup and positive-target framing -/

structure ForeignLookupFrame
    (before after : State catalog Ambient) (actor : sig.Name) : Prop where
  lookup : ∀ {name : sig.Name} {fiber : Fiber catalog},
    before.registry name = some fiber → name ≠ actor →
      after.registry name = some fiber

theorem ProgramActivation.foreignLookupFrame
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (activation : ProgramActivation program before) :
    ForeignLookupFrame before activation.after program.owner := by
  constructor
  intro name fiber present different
  cases activation with
  | begin ownerFiber guard rootAligned =>
      simpa [ProgramActivation.after, setPhase_lookup_other, different] using present
  | landing aligned => exact aligned.foreign_present_after different present

theorem ForeignLookupFrame.activeProvider_forward
    {before after : State catalog Ambient} {actor : sig.Name}
    (frame : ForeignLookupFrame before after actor)
    {actorFiber : Fiber catalog}
    (actorPresent : before.registry actor = some actorFiber)
    (actorNotActive : ¬actorFiber.Active)
    {key : sig.Key} {provider : sig.Name}
    (activeProvider : ActiveProvider before key provider) :
    ActiveProvider after key provider := by
  obtain ⟨providerFiber, providerPresent, providerActive, tablePresent⟩ := activeProvider
  have different : provider ≠ actor := by
    intro same
    subst provider
    rw [actorPresent] at providerPresent
    have fiberEq := Option.some.inj providerPresent
    subst providerFiber
    exact actorNotActive providerActive
  exact ⟨providerFiber, frame.lookup providerPresent different, providerActive, tablePresent⟩

theorem ForeignLookupFrame.targetView_some_forward
    {before after : State catalog Ambient} {actor : sig.Name}
    (frame : ForeignLookupFrame before after actor)
    (beforeWf : WellFormed before) (afterWf : WellFormed after)
    {actorFiber : Fiber catalog}
    (actorPresent : before.registry actor = some actorFiber)
    (actorNotActive : ¬actorFiber.Active)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ actor) (namePresent : before.registry name = some fiber)
    {committed : CommittedView (catalog.declaration fiber.component)}
    (target : targetView before name fiber = some committed) :
    after.registry name = some fiber ∧ targetView after name fiber = some committed := by
  have nameAfter := frame.lookup namePresent different
  refine ⟨nameAfter, targetView_eq_of_isTarget afterWf ?_⟩
  let sourceTarget := targetView_sound beforeWf target
  exact {
    present := nameAfter
    not_retired := sourceTarget.not_retired
    resolves_active := by
      intro declared
      exact frame.activeProvider_forward actorPresent actorNotActive
        (sourceTarget.resolves_active declared)
  }

theorem ProgramActivation.foreign_target
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (activation : ProgramActivation program before)
    (inertia : InertiaPolicy dynamics) (wf : WellFormed before)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ program.owner) (present : before.registry name = some fiber)
    {committed : CommittedView (catalog.declaration fiber.component)}
    (target : targetView before name fiber = some committed) :
    activation.after.registry name = some fiber ∧
      targetView activation.after name fiber = some committed :=
  activation.foreignLookupFrame.targetView_some_forward wf
    (activation.preservesWellFormed inertia wf) activation.source_present
    activation.source_not_active different present target

/-! ## Fixed-program endpoint and rule determinism -/

private theorem setPhase_eq_of_fiber_phase_eq
    (state : State catalog Ambient) (name : sig.Name)
    (leftFiber rightFiber : Fiber catalog) (fiberEq : leftFiber = rightFiber)
    (leftPhase : Phase (catalog.declaration leftFiber.component))
    (rightPhase : Phase (catalog.declaration rightFiber.component))
    (phaseEq : fiberEq ▸ leftPhase = rightPhase) :
    setPhase state name leftFiber leftPhase = setPhase state name rightFiber rightPhase := by
  cases fiberEq
  cases phaseEq
  rfl

private theorem reloading_phase_transport
    (source leftAfter rightAfter : Fiber catalog) (afterEq : leftAfter = rightAfter)
    (leftComponent : leftAfter.component = source.component)
    (rightComponent : rightAfter.component = source.component)
    (leftUndo rightUndo : UndoCode sig) (undoEq : leftUndo = rightUndo)
    (next : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration source.component)) :
    afterEq ▸ Phase.reloading next (leftUndo :: undos)
        (leftComponent.symm ▸ committed) =
      Phase.reloading next (rightUndo :: undos)
        (rightComponent.symm ▸ committed) := by
  cases afterEq
  cases undoEq
  have componentProofEq : leftComponent = rightComponent := Subsingleton.elim _ _
  cases componentProofEq
  rfl

private theorem active_phase_transport
    (source leftAfter rightAfter : Fiber catalog) (afterEq : leftAfter = rightAfter)
    (leftComponent : leftAfter.component = source.component)
    (rightComponent : rightAfter.component = source.component)
    (leftUndo rightUndo : UndoCode sig) (undoEq : leftUndo = rightUndo)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration source.component)) :
    afterEq ▸ Phase.active (leftUndo :: undos)
        (leftComponent.symm ▸ committed) =
      Phase.active (rightUndo :: undos)
        (rightComponent.symm ▸ committed) := by
  cases afterEq
  cases undoEq
  have componentProofEq : leftComponent = rightComponent := Subsingleton.elim _ _
  cases componentProofEq
  rfl

private theorem aligned_after_unique
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (left right : ProgramAlignedLandingActivation program before) :
    left.after = right.after := by
  obtain ⟨leftFiber, leftPresent, leftCode, leftUndos, leftCommitted, leftPhase,
    leftTarget, leftLanding, leftWitness, leftOutcome⟩ := left
  obtain ⟨rightFiber, rightPresent, rightCode, rightUndos, rightCommitted, rightPhase,
    rightTarget, rightLanding, rightWitness, rightOutcome⟩ := right
  rw [leftPresent] at rightPresent
  have fiberEq : leftFiber = rightFiber := Option.some.inj rightPresent
  subst rightFiber
  have phaseEq := leftPhase.symm.trans rightPhase
  injection phaseEq with codeEq undosEq committedEq
  subst rightCode
  subst rightUndos
  subst rightCommitted
  have stepEq : leftLanding.step = rightLanding.step := leftWitness.step_eq rightWitness
  have stepAfterEq := congrArg IterationStep.after stepEq
  have stepUndoEq := congrArg IterationStep.undo stepEq
  have stepNextEq := congrArg IterationStep.next stepEq
  have rightAfterPresent :
      leftLanding.step.after.registry program.owner = some rightLanding.afterFiber := by
    rw [stepAfterEq]
    exact rightLanding.after_present
  rw [leftLanding.after_present] at rightAfterPresent
  have afterFiberEq : leftLanding.afterFiber = rightLanding.afterFiber :=
    Option.some.inj rightAfterPresent
  cases leftOutcome with
  | iter leftNext leftContinues =>
      cases rightOutcome with
      | iter rightNext rightContinues =>
          have nextEq : leftNext = rightNext := Option.some.inj
            (leftContinues.symm.trans (stepNextEq.trans rightContinues))
          subst rightNext
          simp only [ProgramAlignedLandingActivation.after,
            ProgramAlignedLandingActivation.nextPhase]
          rw [stepAfterEq]
          apply setPhase_eq_of_fiber_phase_eq _ _ _ _ afterFiberEq
          exact reloading_phase_transport leftFiber leftLanding.afterFiber
            rightLanding.afterFiber afterFiberEq leftLanding.component_eq
            rightLanding.component_eq leftLanding.step.undo rightLanding.step.undo
            stepUndoEq leftNext leftUndos leftCommitted
      | finish rightDone =>
          have impossible : some leftNext = none :=
            leftContinues.symm.trans (stepNextEq.trans rightDone)
          cases impossible
  | finish leftDone =>
      cases rightOutcome with
      | iter rightNext rightContinues =>
          have impossible : none = some rightNext :=
            leftDone.symm.trans (stepNextEq.trans rightContinues)
          cases impossible
      | finish rightDone =>
          simp only [ProgramAlignedLandingActivation.after,
            ProgramAlignedLandingActivation.nextPhase]
          rw [stepAfterEq]
          apply setPhase_eq_of_fiber_phase_eq _ _ _ _ afterFiberEq
          exact active_phase_transport leftFiber leftLanding.afterFiber
            rightLanding.afterFiber afterFiberEq leftLanding.component_eq
            rightLanding.component_eq leftLanding.step.undo rightLanding.step.undo
            stepUndoEq leftUndos leftCommitted

private theorem begin_landing_impossible
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} {fiber : Fiber catalog}
    (guard : BeginGuard before program.owner fiber)
    (aligned : ProgramAlignedLandingActivation program before) : False := by
  have fiberEq : fiber = aligned.fiber :=
    Option.some.inj (guard.present.symm.trans aligned.present)
  have beginNotInstalled : ¬fiber.Installed := by
    rw [Fiber.Installed, guard.entry]
    simp [Phase.Installed]
  have alignedInstalled : aligned.fiber.Installed := by
    rw [Fiber.Installed, aligned.phase]
    trivial
  have installedIff : fiber.Installed ↔ aligned.fiber.Installed := by rw [fiberEq]
  exact beginNotInstalled (installedIff.2 alignedInstalled)

theorem ProgramActivation.after_unique
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (left right : ProgramActivation program before) : left.after = right.after := by
  cases left with
  | begin leftFiber leftGuard leftRoot =>
      cases right with
      | begin rightFiber rightGuard rightRoot =>
          cases leftGuard with
          | mk leftPresent leftCommitted leftEntry leftTarget =>
              cases rightGuard with
              | mk rightPresent rightCommitted rightEntry rightTarget =>
                  rw [leftPresent] at rightPresent
                  have fiberEq : leftFiber = rightFiber := Option.some.inj rightPresent
                  subst rightFiber
                  rw [leftTarget] at rightTarget
                  have committedEq := Option.some.inj rightTarget
                  subst rightCommitted
                  rfl
      | landing aligned => exact False.elim (begin_landing_impossible leftGuard aligned)
  | landing leftAligned =>
      cases right with
      | begin rightFiber rightGuard rightRoot =>
          exact False.elim (begin_landing_impossible rightGuard leftAligned)
      | landing rightAligned => exact aligned_after_unique leftAligned rightAligned

private theorem aligned_rule_unique
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (left right : ProgramAlignedLandingActivation program before) : left.rule = right.rule := by
  obtain ⟨leftFiber, leftPresent, leftCode, leftUndos, leftCommitted, leftPhase,
    leftTarget, leftLanding, leftWitness, leftOutcome⟩ := left
  obtain ⟨rightFiber, rightPresent, rightCode, rightUndos, rightCommitted, rightPhase,
    rightTarget, rightLanding, rightWitness, rightOutcome⟩ := right
  rw [leftPresent] at rightPresent
  have fiberEq : leftFiber = rightFiber := Option.some.inj rightPresent
  subst rightFiber
  have phaseEq := leftPhase.symm.trans rightPhase
  injection phaseEq with codeEq undosEq committedEq
  subst rightCode
  have stepEq : leftLanding.step = rightLanding.step := leftWitness.step_eq rightWitness
  have stepNextEq := congrArg IterationStep.next stepEq
  cases leftOutcome with
  | iter leftNext leftContinues =>
      cases rightOutcome with
      | iter rightNext rightContinues => rfl
      | finish rightDone =>
          have impossible : some leftNext = none :=
            leftContinues.symm.trans (stepNextEq.trans rightDone)
          cases impossible
  | finish leftDone =>
      cases rightOutcome with
      | iter rightNext rightContinues =>
          have impossible : none = some rightNext :=
            leftDone.symm.trans (stepNextEq.trans rightContinues)
          cases impossible
      | finish rightDone => rfl

theorem ProgramActivation.rule_unique
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (left right : ProgramActivation program before) : left.rule = right.rule := by
  cases left with
  | begin leftFiber leftGuard leftRoot =>
      cases right with
      | begin => rfl
      | landing aligned => exact False.elim (begin_landing_impossible leftGuard aligned)
  | landing leftAligned =>
      cases right with
      | begin rightFiber rightGuard rightRoot =>
          exact False.elim (begin_landing_impossible rightGuard leftAligned)
      | landing rightAligned => exact aligned_rule_unique leftAligned rightAligned

/-! ## Branch-minimal swap laws and structural Begin transport -/

structure ActivationSwapLaws
    {dynamics : Dynamics sig catalog Ambient} {leftProgram rightProgram : Program dynamics}
    {origin : State catalog Ambient}
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin) : Prop where
  left_phase : left.UsesIterator → ForeignPhaseCompatibility leftProgram
  right_phase : right.UsesIterator → ForeignPhaseCompatibility rightProgram
  exact : left.UsesIterator → right.UsesIterator →
    ForwardLifecycleIndependent leftProgram rightProgram

private def moveBeginAcross
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {beginProgram foreignProgram : Program dynamics} {origin : State catalog Ambient}
    (wf : WellFormed origin)
    (foreign : ProgramActivation foreignProgram origin)
    (fiber : Fiber catalog) (guard : BeginGuard origin beginProgram.owner fiber)
    (rootAligned : beginProgram.root = (catalog.declaration fiber.component).entry)
    (different : beginProgram.owner ≠ foreignProgram.owner) :
    ProgramActivation beginProgram foreign.after := by
  have targetAfter := foreign.foreign_target inertia wf different guard.present guard.target
  exact .begin fiber {
    present := targetAfter.1
    committed := guard.committed
    entry := guard.entry
    target := targetAfter.2
  } rootAligned

/-! ## Exact all-nine common-source diamond -/

structure ProgramActivationDiamond
    {dynamics : Dynamics sig catalog Ambient}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin) where
  rightAfterLeft : ProgramActivation rightProgram left.after
  leftAfterRight : ProgramActivation leftProgram right.after
  endpoint_eq : rightAfterLeft.after = leftAfterRight.after

noncomputable def program_activation_diamond
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws left right) : ProgramActivationDiamond left right := by
  cases left with
  | begin leftFiber leftGuard leftRoot =>
      let leftOriginal : ProgramActivation leftProgram origin :=
        .begin leftFiber leftGuard leftRoot
      cases right with
      | begin rightFiber rightGuard rightRoot =>
          let rightOriginal : ProgramActivation rightProgram origin :=
            .begin rightFiber rightGuard rightRoot
          let rightMoved := moveBeginAcross (inertia := inertia) originWf leftOriginal
            rightFiber rightGuard
            rightRoot (Ne.symm different)
          let leftMoved := moveBeginAcross (inertia := inertia) originWf rightOriginal
            leftFiber leftGuard
            leftRoot different
          refine ⟨rightMoved, leftMoved, ?_⟩
          change setPhase
              (setPhase origin leftProgram.owner leftFiber
                (.reloading (catalog.declaration leftFiber.component).entry []
                  leftGuard.committed))
              rightProgram.owner rightFiber
                (.reloading (catalog.declaration rightFiber.component).entry []
                  rightGuard.committed) =
            setPhase
              (setPhase origin rightProgram.owner rightFiber
                (.reloading (catalog.declaration rightFiber.component).entry []
                  rightGuard.committed))
              leftProgram.owner leftFiber
                (.reloading (catalog.declaration leftFiber.component).entry []
                  leftGuard.committed)
          exact setPhase_commute origin leftProgram.owner rightProgram.owner leftFiber rightFiber
            _ _ different
      | landing rightAligned =>
          let rightOriginal : ProgramActivation rightProgram origin := .landing rightAligned
          let leftPhase : Phase (catalog.declaration leftFiber.component) :=
            .reloading (catalog.declaration leftFiber.component).entry [] leftGuard.committed
          let framed :=
            Cordis.GlobalForeignPhase.ForeignPhaseCompatibility.frame
              (laws.right_phase trivial) rightAligned.landing.step leftProgram.owner leftFiber
              leftPhase rightAligned.program_witness.reachable leftGuard.present different
              rightAligned.program_witness.program_executed
          have rightSourceAndTarget := leftOriginal.foreign_target inertia originWf
            (Ne.symm different) rightAligned.present rightAligned.target
          have rightAfterPresent :
              framed.movedStep.after.registry rightProgram.owner =
                some rightAligned.landing.afterFiber := by
            rw [framed.after_eq]
            exact (setPhase_lookup_other rightAligned.landing.step.after leftProgram.owner
              rightProgram.owner leftFiber leftPhase (Ne.symm different)).trans
                rightAligned.landing.after_present
          let rightMovedPack := reframeActivation rightAligned framed rightSourceAndTarget.1
            rightSourceAndTarget.2 rightAfterPresent
            (Cordis.GlobalLandingTransposition.LifecycleYieldAgrees.refl
              rightAligned.landing.step)
          let leftMoved := moveBeginAcross (inertia := inertia) originWf rightOriginal
            leftFiber leftGuard
            leftRoot different
          refine ⟨.landing rightMovedPack.activation, leftMoved, ?_⟩
          change rightMovedPack.activation.after = leftMoved.after
          rw [rightMovedPack.after_eq, framed.after_eq]
          change setPhase
              (setPhase rightAligned.landing.step.after leftProgram.owner leftFiber leftPhase)
              rightProgram.owner rightAligned.landing.afterFiber rightAligned.nextPhase =
            setPhase
              (setPhase rightAligned.landing.step.after rightProgram.owner
                rightAligned.landing.afterFiber rightAligned.nextPhase)
              leftProgram.owner leftFiber leftPhase
          exact setPhase_commute rightAligned.landing.step.after leftProgram.owner
            rightProgram.owner leftFiber rightAligned.landing.afterFiber leftPhase
            rightAligned.nextPhase different
  | landing leftAligned =>
      let leftOriginal : ProgramActivation leftProgram origin := .landing leftAligned
      cases right with
      | begin rightFiber rightGuard rightRoot =>
          let rightOriginal : ProgramActivation rightProgram origin :=
            .begin rightFiber rightGuard rightRoot
          let rightPhase : Phase (catalog.declaration rightFiber.component) :=
            .reloading (catalog.declaration rightFiber.component).entry [] rightGuard.committed
          let framed :=
            Cordis.GlobalForeignPhase.ForeignPhaseCompatibility.frame
              (laws.left_phase trivial) leftAligned.landing.step rightProgram.owner rightFiber
              rightPhase leftAligned.program_witness.reachable rightGuard.present
              (Ne.symm different) leftAligned.program_witness.program_executed
          have leftSourceAndTarget := rightOriginal.foreign_target inertia originWf different
            leftAligned.present leftAligned.target
          have leftAfterPresent :
              framed.movedStep.after.registry leftProgram.owner =
                some leftAligned.landing.afterFiber := by
            rw [framed.after_eq]
            exact (setPhase_lookup_other leftAligned.landing.step.after rightProgram.owner
              leftProgram.owner rightFiber rightPhase different).trans
                leftAligned.landing.after_present
          let leftMovedPack := reframeActivation leftAligned framed leftSourceAndTarget.1
            leftSourceAndTarget.2 leftAfterPresent
            (Cordis.GlobalLandingTransposition.LifecycleYieldAgrees.refl
              leftAligned.landing.step)
          let rightMoved := moveBeginAcross (inertia := inertia) originWf leftOriginal
            rightFiber rightGuard
            rightRoot (Ne.symm different)
          refine ⟨rightMoved, .landing leftMovedPack.activation, ?_⟩
          change rightMoved.after = leftMovedPack.activation.after
          rw [leftMovedPack.after_eq, framed.after_eq]
          change setPhase
              (setPhase leftAligned.landing.step.after leftProgram.owner
                leftAligned.landing.afterFiber leftAligned.nextPhase)
              rightProgram.owner rightFiber rightPhase =
            setPhase
              (setPhase leftAligned.landing.step.after rightProgram.owner rightFiber rightPhase)
              leftProgram.owner leftAligned.landing.afterFiber leftAligned.nextPhase
          exact setPhase_commute leftAligned.landing.step.after leftProgram.owner
            rightProgram.owner leftAligned.landing.afterFiber rightFiber leftAligned.nextPhase
            rightPhase different
      | landing rightAligned =>
          let landingDiamond := landing_activation_diamond (inertia := inertia) originWf different
            (laws.exact trivial trivial) (laws.left_phase trivial) (laws.right_phase trivial)
            leftAligned rightAligned
          exact {
            rightAfterLeft := .landing landingDiamond.rightAfterLeft
            leftAfterRight := .landing landingDiamond.leftAfterRight
            endpoint_eq := landingDiamond.left_then_right.trans
              landingDiamond.right_then_left.symm
          }

/-! ## Paper-shaped actual-second-step transposition -/

structure ProgramActivationTransposition
    {dynamics : Dynamics sig catalog Ambient}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin) where
  leftAfterRight : ProgramActivation leftProgram rightAtOrigin.after
  endpoint_eq : leftAfterRight.after = rightAfterLeft.after

noncomputable def transpose_program_activations
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws leftAtOrigin rightAtOrigin) :
    ProgramActivationTransposition leftAtOrigin rightAfterLeft rightAtOrigin := by
  let diamond := program_activation_diamond (inertia := inertia) originWf different
    leftAtOrigin rightAtOrigin laws
  have normalEndpoint := diamond.rightAfterLeft.after_unique rightAfterLeft
  exact {
    leftAfterRight := diamond.leftAfterRight
    endpoint_eq := diamond.endpoint_eq.symm.trans normalEndpoint
  }

def ProgramActivationTransposition.swappedTransition
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    {leftAtOrigin : ProgramActivation leftProgram origin}
    {rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after}
    {rightAtOrigin : ProgramActivation rightProgram origin}
    (result : ProgramActivationTransposition leftAtOrigin rightAfterLeft rightAtOrigin) :
    Transition dynamics inertia rightAtOrigin.after rightAfterLeft.after :=
  result.endpoint_eq ▸ result.leftAfterRight.transition inertia

/-! ## Positive branch coverage -/

namespace Example

namespace LandingPair

abbrev dynamics := Cordis.GlobalLandingTransposition.Example.dynamics
abbrev inertia := Cordis.GlobalLandingTransposition.Example.inertia
abbrev leftProgram := Cordis.GlobalLandingTransposition.Example.leftProgram
abbrev rightProgram := Cordis.GlobalLandingTransposition.Example.rightProgram
abbrev origin := Cordis.GlobalLandingTransposition.Example.origin

def left : ProgramActivation leftProgram origin :=
  .landing Cordis.GlobalLandingTransposition.Example.leftActivation

def right : ProgramActivation rightProgram origin :=
  .landing Cordis.GlobalLandingTransposition.Example.rightActivation

theorem laws : ActivationSwapLaws left right where
  left_phase _ := Cordis.GlobalLandingTransposition.Example.leftCompatible
  right_phase _ := Cordis.GlobalLandingTransposition.Example.rightCompatible
  exact _ _ := Cordis.GlobalLandingTransposition.Example.forwardLifecycleIndependent

noncomputable def diamond : ProgramActivationDiamond left right :=
  program_activation_diamond (inertia := inertia)
    Cordis.GlobalLandingTransposition.Example.origin_wellFormed (by decide) left right laws

noncomputable def transposition :
    ProgramActivationTransposition left diamond.rightAfterLeft right :=
  transpose_program_activations (inertia := inertia)
    Cordis.GlobalLandingTransposition.Example.origin_wellFormed (by decide)
    left diamond.rightAfterLeft right laws

noncomputable def swappedTransition :
    Transition dynamics inertia right.after diamond.rightAfterLeft.after :=
  transposition.swappedTransition

def executableRulePair : Rule × Rule := (left.rule, right.rule)

theorem executableRulePair_eq : executableRulePair = (.iter, .finish) := rfl

end LandingPair

namespace BeginPairs

abbrev Signature := Cordis.GlobalLandingTransposition.Example.Signature
abbrev exampleCatalog := Cordis.GlobalLandingTransposition.Example.exampleCatalog
abbrev ExampleState := Cordis.GlobalLandingTransposition.Example.ExampleState
abbrev dynamics := Cordis.GlobalLandingTransposition.Example.dynamics
abbrev inertia := Cordis.GlobalLandingTransposition.Example.inertia
abbrev leftProgram := Cordis.GlobalLandingTransposition.Example.leftProgram
abbrev rightProgram := Cordis.GlobalLandingTransposition.Example.rightProgram

def emptyView := Cordis.GlobalLandingTransposition.Example.emptyView

def inactiveFiber (birth : Nat) : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := birth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def beginOrigin : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false (inactiveFiber 0)) true (inactiveFiber 1)

@[simp] theorem begin_left_present :
    beginOrigin.registry false = some (inactiveFiber 0) := by simp [beginOrigin]

@[simp] theorem begin_right_present :
    beginOrigin.registry true = some (inactiveFiber 1) := by simp [beginOrigin]

theorem beginOrigin_wellFormed : WellFormed beginOrigin := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [beginOrigin] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [beginOrigin] at lookup <;> subst fiber <;>
      simp [inactiveFiber] at parentEq
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [beginOrigin] at lookup <;> subst fiber <;>
      simp [inactiveFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases leftFiber.component
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    rcases declared with ⟨key, required⟩
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required

theorem begin_left_target :
    targetView beginOrigin false (inactiveFiber 0) = some emptyView := by
  apply targetView_eq_of_isTarget beginOrigin_wellFormed
  exact {
    present := begin_left_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  }

theorem begin_right_target :
    targetView beginOrigin true (inactiveFiber 1) = some emptyView := by
  apply targetView_eq_of_isTarget beginOrigin_wellFormed
  exact {
    present := begin_right_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  }

def beginLeft : ProgramActivation leftProgram beginOrigin := .begin (inactiveFiber 0) {
  present := begin_left_present
  committed := emptyView
  entry := rfl
  target := begin_left_target
} rfl

def beginRight : ProgramActivation rightProgram beginOrigin := .begin (inactiveFiber 1) {
  present := begin_right_present
  committed := emptyView
  entry := rfl
  target := begin_right_target
} rfl

theorem beginBeginLaws : ActivationSwapLaws beginLeft beginRight where
  left_phase impossible := False.elim impossible
  right_phase impossible := False.elim impossible
  exact impossible := False.elim impossible

noncomputable def beginBeginDiamond : ProgramActivationDiamond beginLeft beginRight :=
  program_activation_diamond (inertia := inertia) beginOrigin_wellFormed (by decide)
    beginLeft beginRight beginBeginLaws

def mixedOrigin : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false (inactiveFiber 0)) true
      (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1)

@[simp] theorem mixed_left_present : mixedOrigin.registry false = some (inactiveFiber 0) := by
  simp [mixedOrigin]

@[simp] theorem mixed_right_present : mixedOrigin.registry true =
    some (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) := by
  simp [mixedOrigin]

theorem mixed_wellFormed : WellFormed mixedOrigin := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [mixedOrigin] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [mixedOrigin] at lookup <;> subst fiber <;>
      simp [inactiveFiber, Cordis.GlobalLandingTransposition.Example.reloadingFiber] at parentEq
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [mixedOrigin] at lookup <;> subst fiber <;>
      simp [inactiveFiber, Cordis.GlobalLandingTransposition.Example.reloadingFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases leftFiber.component
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    rcases declared with ⟨key, required⟩
    simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required

theorem mixed_left_target : targetView mixedOrigin false (inactiveFiber 0) = some emptyView := by
  apply targetView_eq_of_isTarget mixed_wellFormed
  exact {
    present := mixed_left_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  }

theorem mixed_right_target : targetView mixedOrigin true
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) = some emptyView := by
  apply targetView_eq_of_isTarget mixed_wellFormed
  exact {
    present := mixed_right_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at required
  }

def mixedRightStep : IterationStep dynamics true () mixedOrigin :=
  Cordis.GlobalLandingTransposition.Example.step true mixedOrigin
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) mixed_right_present

theorem mixedRightStep_executed :
    executeOne dynamics (Cordis.GlobalLandingTransposition.Example.oracle true) () mixedOrigin =
      .ok mixedRightStep :=
  Cordis.GlobalLandingTransposition.Example.step_executed true mixedOrigin
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) mixed_right_present

def mixedRightLanding : Landing dynamics true () mixedOrigin
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) where
  RegistrationError := Unit
  oracle := Cordis.GlobalLandingTransposition.Example.oracle true
  step := mixedRightStep
  executed := mixedRightStep_executed
  before_present := mixed_right_present
  afterFiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 1
  after_present := mixed_right_present
  component_eq := rfl
  phase_eq := rfl

def mixedBegin : ProgramActivation leftProgram mixedOrigin := .begin (inactiveFiber 0) {
  present := mixed_left_present
  committed := emptyView
  entry := rfl
  target := mixed_left_target
} rfl

def mixedFinishAligned : ProgramAlignedLandingActivation rightProgram mixedOrigin where
  fiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 1
  present := mixed_right_present
  code := ()
  undos := []
  committed := emptyView
  phase := rfl
  target := mixed_right_target
  landing := mixedRightLanding
  program_witness := ⟨Reach.root, mixedRightStep_executed⟩
  outcome := .finish rfl

def mixedFinish : ProgramActivation rightProgram mixedOrigin := .landing mixedFinishAligned

theorem mixedLaws : ActivationSwapLaws mixedBegin mixedFinish where
  left_phase impossible := False.elim impossible
  right_phase _ := Cordis.GlobalLandingTransposition.Example.rightCompatible
  exact impossible := False.elim impossible

noncomputable def beginFinishDiamond : ProgramActivationDiamond mixedBegin mixedFinish :=
  program_activation_diamond (inertia := inertia) mixed_wellFormed (by decide)
    mixedBegin mixedFinish mixedLaws

end BeginPairs

namespace FinishPair

abbrev Signature := Cordis.GlobalLandingTransposition.Example.Signature
abbrev exampleCatalog := Cordis.GlobalLandingTransposition.Example.exampleCatalog
abbrev ExampleState := Cordis.GlobalLandingTransposition.Example.ExampleState
abbrev origin := Cordis.GlobalLandingTransposition.Example.origin

def result (state : ExampleState) : OrdinaryResult exampleCatalog Bool where
  after := state
  undo := .observe false
  next := none

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result state))

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := Cordis.GlobalLandingTransposition.YieldSyntaxGap.ambientSetoid
  runIterator := runIterator
  applyExternalUndo := Cordis.GlobalLandingTransposition.YieldSyntaxGap.applyExternalUndo
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        rfl
  externalUndo_respects := by
    intro undo left right related
    cases undo with
    | restore ambient => rfl
    | observe tag => exact related
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact {
          beforeFiber := current
          afterFiber := current
          before_present := lookup
          after_present := lookup
          component_eq := rfl
          parent_eq := rfl
          birth_eq := rfl
          retired_eq := rfl
          phase_eq := rfl
          other_unchanged := by intros; rfl
          table_writes := by
            unfold WritesWithinProvision
            intros
            rfl
          nextBirth_eq := rfl
        }
  ordinary_preserves_wellFormed := by
    intro owner code state found runEq wf
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact wf
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary related rfl rfl)
  ReadEquivalent _ left right := left.ambient = right.ambient
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary related rfl rfl)
  retire_respects := by
    intro name left right related
    exact Cordis.GlobalLandingTransposition.YieldSyntaxGap.dynamics.retire_respects name related

def oracle (owner : Bool) : RegistrationOracle dynamics owner Unit where
  certify _ _ := .error ()

def program (owner : Bool) : Program dynamics where
  owner := owner
  RegistrationError := Unit
  oracle := oracle owner
  root := ()

abbrev leftProgram := program false
abbrev rightProgram := program true

theorem run_success
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    dynamics.runIterator owner () state = .ok (.ordinary (result state)) := by
  simp [dynamics, runIterator, present]

def step
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    IterationStep dynamics owner () state where
  after := state
  undo := .external (.observe false)
  next := none
  source := .ordinary (result state) (run_success owner state fiber present)
  recovers := rfl
  preserves_wellFormed := fun wf ↦ wf

theorem step_executed
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    executeOne dynamics (oracle owner) () state = .ok (step owner state fiber present) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state fiber present)
  · rename_i found foundEq
    have resultEq : found = result state :=
      IteratorResult.ordinary.inj
        (Except.ok.inj (foundEq.symm.trans (run_success owner state fiber present)))
    subst found
    have proofEq : foundEq = run_success owner state fiber present := Subsingleton.elim _ _
    cases proofEq
    rfl
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state fiber present)

theorem forward_apply (owner : Bool) (state : ExampleState) :
    forward (program owner) () state =
      match state.registry owner with
      | none => none
      | some _ => some state := by
  unfold forward
  simp only [program]
  cases lookup : state.registry owner with
  | none =>
      have raw : dynamics.runIterator owner () state = .error () := by
        simp [dynamics, runIterator, lookup]
      have failed : executeOne dynamics (oracle owner) () state = .error (.iterator ()) := by
        rw [executeOne.eq_def]
        split <;> simp_all
      rw [failed]
  | some fiber =>
      rw [step_executed owner state fiber lookup]
      rfl

theorem forward_success_eq
    (owner : Bool) (state moved : ExampleState)
    (transformed : forward (program owner) () state = some moved) : moved = state := by
  rw [forward_apply] at transformed
  cases lookup : state.registry owner with
  | none => simp [lookup] at transformed
  | some fiber =>
      simp [lookup] at transformed
      exact transformed.symm

theorem inverse_identity
    {owner : Bool} {state : ExampleState}
    {current : IterationStep dynamics owner () state}
    (executed : executeOne dynamics (oracle owner) () state = .ok current) :
    total (dynamics.applyUndo current.undo) =
      (Cordis.PartialTransformation.identity : PartialMap exampleCatalog Bool) := by
  obtain ⟨fiber, present⟩ := GlobalForeignPhase.IterationStep.owner_present current
  have known := step_executed owner state fiber present
  have currentEq : current = step owner state fiber present :=
    Except.ok.inj (executed.symm.trans known)
  subst current
  rfl

theorem forwards_commute (leftOwner rightOwner : Bool) :
    Cordis.PartialTransformation.Commutes
      (forward (program leftOwner) ()) (forward (program rightOwner) ()) := by
  intro state
  unfold Cordis.PartialTransformation.comp
  rw [forward_apply, forward_apply]
  cases leftLookup : state.registry leftOwner <;>
    cases rightLookup : state.registry rightOwner <;>
      simp [forward_apply, leftLookup, rightLookup]

theorem generators_commute
    {leftMap rightMap : PartialMap exampleCatalog Bool}
    (leftGenerated : Generator leftProgram leftMap)
    (rightGenerated : Generator rightProgram rightMap) :
    Cordis.PartialTransformation.Commutes leftMap rightMap := by
  cases leftGenerated with
  | forward leftReachable =>
      cases rightGenerated with
      | forward rightReachable =>
          exact forwards_commute false true
      | inverse rightReachable rightExecuted =>
          rw [inverse_identity rightExecuted]
          exact Cordis.GlobalLandingTransposition.YieldSyntaxGap.identity_commutes_left _
  | inverse leftReachable leftExecuted =>
      rw [inverse_identity leftExecuted]
      cases rightGenerated with
      | forward rightReachable =>
          exact (Cordis.GlobalLandingTransposition.YieldSyntaxGap.identity_commutes_left _).symm
      | inverse rightReachable rightExecuted =>
          rw [inverse_identity rightExecuted]
          exact Cordis.GlobalLandingTransposition.YieldSyntaxGap.identity_commutes_left _

theorem generator_stable
    (owner foreignOwner : Bool) {map : PartialMap exampleCatalog Bool}
    (generated : Generator (program foreignOwner) map) : YieldStable (program owner) map := by
  intro code reachable seed current moved executed transformed
  cases code
  cases generated with
  | forward foreignReachable =>
      have movedEq := forward_success_eq foreignOwner seed moved transformed
      subst moved
      exact ⟨current, executed, YieldAgrees.refl current⟩
  | inverse foreignReachable foreignExecuted =>
      rw [inverse_identity foreignExecuted] at transformed
      have movedEq := Option.some.inj transformed
      subst moved
      exact ⟨current, executed, YieldAgrees.refl current⟩

theorem independent : Independent leftProgram rightProgram :=
  Independent.of_generators generators_commute
    (generator_stable false true) (generator_stable true false)

theorem lifecycleStable (owner foreignOwner : Bool) :
    LifecycleYieldStable (program owner) (forward (program foreignOwner) ()) := by
  intro code reachable seed current moved executed transformed
  cases code
  have movedEq := forward_success_eq foreignOwner seed moved transformed
  subst moved
  exact ⟨current, executed, GlobalLandingTransposition.LifecycleYieldAgrees.refl current⟩

theorem exact : ForwardLifecycleIndependent leftProgram rightProgram where
  independent := independent
  left_under_right := by intro code reachable; cases code; exact lifecycleStable false true
  right_under_left := by intro code reachable; cases code; exact lifecycleStable true false

theorem compatible (owner : Bool) : ForeignPhaseCompatibility (program owner) where
  execute_setPhase := by
    intro code state current foreignName foreignFiber foreignPhase reachable foreignPresent
      different executed
    cases code
    obtain ⟨ownerFiber, ownerPresent⟩ := GlobalForeignPhase.IterationStep.owner_present current
    have movedOwnerPresent :
        (setPhase state foreignName foreignFiber foreignPhase).registry owner =
          some ownerFiber := by
      rw [setPhase_lookup_other state foreignName owner foreignFiber foreignPhase
        (Ne.symm different)]
      exact ownerPresent
    have known := step_executed owner state ownerFiber ownerPresent
    have currentEq : current = step owner state ownerFiber ownerPresent :=
      Except.ok.inj (executed.symm.trans known)
    subst current
    let moved := step owner (setPhase state foreignName foreignFiber foreignPhase)
      ownerFiber movedOwnerPresent
    exact ⟨moved,
      step_executed owner (setPhase state foreignName foreignFiber foreignPhase)
        ownerFiber movedOwnerPresent, ⟨rfl, rfl, rfl⟩, rfl⟩

def leftStep := step false origin
  (Cordis.GlobalLandingTransposition.Example.reloadingFiber 0)
  Cordis.GlobalLandingTransposition.Example.left_present

def rightStep := step true origin
  (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1)
  Cordis.GlobalLandingTransposition.Example.right_present

def leftLanding : Landing dynamics false () origin
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 0) where
  RegistrationError := Unit
  oracle := oracle false
  step := leftStep
  executed := step_executed false origin _
    Cordis.GlobalLandingTransposition.Example.left_present
  before_present := Cordis.GlobalLandingTransposition.Example.left_present
  afterFiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 0
  after_present := Cordis.GlobalLandingTransposition.Example.left_present
  component_eq := rfl
  phase_eq := rfl

def rightLanding : Landing dynamics true () origin
    (Cordis.GlobalLandingTransposition.Example.reloadingFiber 1) where
  RegistrationError := Unit
  oracle := oracle true
  step := rightStep
  executed := step_executed true origin _
    Cordis.GlobalLandingTransposition.Example.right_present
  before_present := Cordis.GlobalLandingTransposition.Example.right_present
  afterFiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 1
  after_present := Cordis.GlobalLandingTransposition.Example.right_present
  component_eq := rfl
  phase_eq := rfl

def leftAligned : ProgramAlignedLandingActivation leftProgram origin where
  fiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 0
  present := Cordis.GlobalLandingTransposition.Example.left_present
  code := ()
  undos := []
  committed := Cordis.GlobalLandingTransposition.Example.emptyView
  phase := rfl
  target := Cordis.GlobalLandingTransposition.Example.left_target
  landing := leftLanding
  program_witness := ⟨Reach.root, leftLanding.executed⟩
  outcome := .finish rfl

def rightAligned : ProgramAlignedLandingActivation rightProgram origin where
  fiber := Cordis.GlobalLandingTransposition.Example.reloadingFiber 1
  present := Cordis.GlobalLandingTransposition.Example.right_present
  code := ()
  undos := []
  committed := Cordis.GlobalLandingTransposition.Example.emptyView
  phase := rfl
  target := Cordis.GlobalLandingTransposition.Example.right_target
  landing := rightLanding
  program_witness := ⟨Reach.root, rightLanding.executed⟩
  outcome := .finish rfl

def left : ProgramActivation leftProgram origin := .landing leftAligned
def right : ProgramActivation rightProgram origin := .landing rightAligned

theorem laws : ActivationSwapLaws left right where
  left_phase _ := compatible false
  right_phase _ := compatible true
  exact _ _ := exact

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

noncomputable def diamond : ProgramActivationDiamond left right :=
  program_activation_diamond (inertia := inertia)
    Cordis.GlobalLandingTransposition.Example.origin_wellFormed
    (by decide : leftProgram.owner ≠ rightProgram.owner) left right laws

end FinishPair

end Example

/-! ## Root alignment and distinct-owner necessity -/

namespace RootProvenanceGap

open Cordis.GlobalRegistry.Example Cordis.GlobalLifecycle.Example

def wrongProgram : Program dynamics where
  owner := 0
  RegistrationError := String
  oracle := oracle
  root := 0

def validGuard : BeginGuard start wrongProgram.owner inactiveProvider where
  present := start_present
  committed := emptyProviderView
  entry := rfl
  target := start_target

theorem root_not_catalog_entry :
    wrongProgram.root ≠ (exampleCatalog.declaration inactiveProvider.component).entry := by
  decide

theorem valid_guard_does_not_supply_root_alignment :
    ¬wrongProgram.root = (exampleCatalog.declaration inactiveProvider.component).entry :=
  root_not_catalog_entry

end RootProvenanceGap

namespace SameOwnerGap

open Cordis.GlobalRegistry.Example Cordis.GlobalLifecycle.Example

def reloadingPhase : Phase providerDecl := .reloading 10 [] emptyProviderView
def activePhase : Phase providerDecl := .active [] emptyProviderView

theorem same_owner_phase_updates_do_not_commute :
    setPhase (setPhase start 0 inactiveProvider reloadingPhase)
        0 inactiveProvider activePhase ≠
      setPhase (setPhase start 0 inactiveProvider activePhase)
        0 inactiveProvider reloadingPhase := by
  intro equal
  have lookupEq := congrArg (fun state ↦ state.registry 0) equal
  have fiberEq := Option.some.inj lookupEq
  let activeFiber : Fiber exampleCatalog := { inactiveProvider with phase := activePhase }
  let reloadingFiber : Fiber exampleCatalog := {
    inactiveProvider with phase := reloadingPhase
  }
  have activeIff : activeFiber.Active ↔ reloadingFiber.Active := by
    change ({ inactiveProvider with phase := activePhase } : Fiber exampleCatalog).Active ↔
      ({ inactiveProvider with phase := reloadingPhase } : Fiber exampleCatalog).Active
    rw [fiberEq]
  have active : activeFiber.Active := by
    simp [activeFiber, activePhase, Fiber.Active, Phase.Active]
  have notReloading : ¬reloadingFiber.Active := by
    simp [reloadingFiber, reloadingPhase, Fiber.Active, Phase.Active]
  exact notReloading (activeIff.1 active)

end SameOwnerGap

/-! ## Bridges to existing necessity models -/

theorem common_source_applicability_is_necessary :
    targetView GlobalLandingTransposition.ProviderFinishGap.before 1
        GlobalLandingTransposition.ProviderFinishGap.consumerFiber ≠
      some GlobalLandingTransposition.ProviderFinishGap.consumerView :=
  GlobalLandingTransposition.ProviderFinishGap.consumer_begin_not_available_at_predecessor

theorem bare_landing_does_not_determine_program :
    ¬LandingProgramWitness GlobalLandingTransposition.OracleProvenanceGap.programOne
      GlobalLandingTransposition.OracleProvenanceGap.landingTwo :=
  GlobalLandingTransposition.OracleProvenanceGap.landingTwo_not_aligned_with_programOne

theorem semantic_independence_does_not_supply_exact_swap_laws :
    ¬ForwardLifecycleIndependent GlobalLandingTransposition.YieldSyntaxGap.leftProgram
      GlobalLandingTransposition.YieldSyntaxGap.rightProgram :=
  GlobalLandingTransposition.YieldSyntaxGap.not_forward_lifecycle_independent

end Cordis.GlobalActivationTransposition
