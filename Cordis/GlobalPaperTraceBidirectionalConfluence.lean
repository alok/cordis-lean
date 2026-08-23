import Cordis.GlobalPaperTraceBidirectionalNormalizer
import Cordis.GlobalPaperTraceConfluence

/-!
# Conditional confluence for bidirectional paper-trace authorities

This module lifts the existing decreasing/local-join Newman kernel to the unified
forward/backward paper-trace authority.  A `ConfluentAuthority` supplies the
rewrite relation selected by each orientation-indexed link, proves that the
authority-selected link is an edge, supplies strict measure decrease and local
joinability, and identifies its normal forms with irreducible packages.

The resulting theorem proves uniqueness of successful terminal packages for the
new bidirectional normalizer.  It does not derive a local join, a rewrite
strategy, a decreasing measure, confluence, Lemma 72, or Theorem 73 from the
CORDIS dynamics.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceBidirectionalConfluence

noncomputable section

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceBidirectionalNormalization

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
variable {values : ValueSetoids sig}
variable {dynamics : Dynamics sig catalog Ambient}
variable {inertia : InertiaPolicy dynamics}
variable {initial : GlobalState catalog Ambient}

abbrev Package
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : GlobalState catalog Ambient) :=
  TracePackage values dynamics inertia initial

abbrev Link
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : GlobalState catalog Ambient) :=
  BidirectionalWitness values dynamics inertia initial

abbrev BaseAuthority
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : GlobalState catalog Ambient) :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Authority
    values dynamics inertia initial

def AuthorityStep
    (authority : BaseAuthority values dynamics inertia initial)
    (source target : Package values dynamics inertia initial) : Prop :=
  ∃ notNormal : ¬ authority.normal source,
    (authority.step source notNormal).val.target dynamics inertia initial = target

def AuthorityLinked
    (authority : BaseAuthority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) :
    List (Link values dynamics inertia initial) → Prop
  | [] => authority.normal source
  | link :: rest =>
      ∃ notNormal : ¬ authority.normal source,
        link = (authority.step source notNormal).val ∧
          AuthorityLinked authority
            ((authority.step source notNormal).val.target dynamics inertia initial) rest

structure ConfluentAuthority
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : GlobalState catalog Ambient) where
  base : BaseAuthority values dynamics inertia initial
  rewrite : Package values dynamics inertia initial →
    Package values dynamics inertia initial → Prop
  selected : ∀ (source : Package values dynamics inertia initial)
    (notNormal : ¬ base.normal source),
    rewrite source ((base.step source notNormal).val.target dynamics inertia initial)
  decreases : ∀ {source target : Package values dynamics inertia initial},
    rewrite source target → base.measure target < base.measure source
  localJoin : ∀ {source left right : Package values dynamics inertia initial},
    rewrite source left → rewrite source right →
      Cordis.GlobalPaperTraceConfluence.Joinable rewrite left right
  normal_iff : ∀ (source : Package values dynamics inertia initial),
    base.normal source ↔
      Cordis.GlobalPaperTraceConfluence.Irreducible rewrite source

def authoritySystem
    (authority : ConfluentAuthority values dynamics inertia initial) :
    Cordis.GlobalPaperTraceConfluence.DecreasingSystem
      (Package values dynamics inertia initial) where
  step := authority.rewrite
  measure := authority.base.measure
  decreases := authority.decreases
  localJoin := authority.localJoin

theorem path_of_authorityLinked
    (authority : BaseAuthority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) :
    ∀ (links : List (Link values dynamics inertia initial)),
      AuthorityLinked authority source links →
        Cordis.GlobalPaperTraceConfluence.Path
          (AuthorityStep authority) source
            (CertifiedChain.terminal dynamics inertia initial source links)
  | [], _ => .refl source
  | link :: rest, evidence => by
      obtain ⟨notNormal, linkEq, tail⟩ := evidence
      subst link
      exact .cons ⟨notNormal, rfl⟩
        (path_of_authorityLinked authority
          ((authority.step source notNormal).val.target dynamics inertia initial)
          rest tail)

theorem path_lift_to_rewrite
    (authority : ConfluentAuthority values dynamics inertia initial)
    {source target : Package values dynamics inertia initial} :
    Cordis.GlobalPaperTraceConfluence.Path
        (AuthorityStep authority.base) source target →
      Cordis.GlobalPaperTraceConfluence.Path authority.rewrite source target := by
  intro path
  induction path with
  | refl node => exact .refl node
  | cons edge tail ih =>
      obtain ⟨notNormal, targetEq⟩ := edge
      cases targetEq
      exact .cons (authority.selected _ notNormal) ih

theorem normalizeFuel_authorityLinked
    (authority : BaseAuthority values dynamics inertia initial) :
    ∀ (fuel : Nat) (source : Package values dynamics inertia initial)
      (result : Cordis.GlobalPaperTraceBidirectionalNormalizer.Result authority source),
      Cordis.GlobalPaperTraceBidirectionalNormalizer.normalizeFuel
          authority fuel source = some result →
        AuthorityLinked authority source result.links
  | 0, source, result, equality => by
      unfold Cordis.GlobalPaperTraceBidirectionalNormalizer.normalizeFuel at equality
      split at equality
      · rename_i normal
        cases equality
        exact normal
      · contradiction
  | fuel + 1, source, result, equality => by
      unfold Cordis.GlobalPaperTraceBidirectionalNormalizer.normalizeFuel at equality
      split at equality
      · rename_i normal
        cases equality
        exact normal
      · rename_i notNormal
        let chosen := authority.step source notNormal
        dsimp [chosen] at equality
        split at equality
        · contradiction
        · rename_i tail tailEquality
          cases result
          cases equality
          refine ⟨notNormal, rfl, ?_⟩
          exact normalizeFuel_authorityLinked authority fuel
            chosen.val.target tail tailEquality

theorem normalize_authorityLinked
    (authority : BaseAuthority values dynamics inertia initial)
    (source : Package values dynamics inertia initial)
    (result : Cordis.GlobalPaperTraceBidirectionalNormalizer.Result authority source)
    (equality : Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize
      authority source = some result) :
    AuthorityLinked authority source result.links := by
  exact normalizeFuel_authorityLinked authority (authority.measure source) source result
    (by simpa [Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize] using equality)

theorem normal_irreducible
    (authority : BaseAuthority values dynamics inertia initial)
    {source : Package values dynamics inertia initial}
    (normal : authority.normal source) :
    Cordis.GlobalPaperTraceConfluence.Irreducible (AuthorityStep authority) source := by
  intro target edge
  exact edge.choose normal

theorem normal_rewrite_irreducible
    (authority : ConfluentAuthority values dynamics inertia initial)
    {source : Package values dynamics inertia initial}
    (normal : authority.base.normal source) :
    Cordis.GlobalPaperTraceConfluence.Irreducible authority.rewrite source :=
  (authority.normal_iff source).mp normal

theorem normalize_results_unique
    (authority : ConfluentAuthority values dynamics inertia initial)
    (source : Package values dynamics inertia initial)
    (left right : Cordis.GlobalPaperTraceBidirectionalNormalizer.Result
      authority.base source)
    (leftEquality : Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize
      authority.base source = some left)
    (rightEquality : Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize
      authority.base source = some right) :
    left.final = right.final := by
  have leftEvidence := normalize_authorityLinked authority.base source left leftEquality
  have rightEvidence := normalize_authorityLinked authority.base source right rightEquality
  have leftPath :
      Cordis.GlobalPaperTraceConfluence.Path authority.rewrite source left.final := by
    rw [← left.terminal_eq]
    exact path_lift_to_rewrite authority
      (path_of_authorityLinked authority.base source left.links leftEvidence)
  have rightPath :
      Cordis.GlobalPaperTraceConfluence.Path authority.rewrite source right.final := by
    rw [← right.terminal_eq]
    exact path_lift_to_rewrite authority
      (path_of_authorityLinked authority.base source right.links rightEvidence)
  exact Cordis.GlobalPaperTraceConfluence.NormalForm.endpoint_eq (authoritySystem authority)
    { endpoint := left.final
      path := leftPath
      irreducible := normal_rewrite_irreducible authority left.normal }
    { endpoint := right.final
      path := rightPath
      irreducible := normal_rewrite_irreducible authority right.normal }

namespace Example

abbrev exampleValues :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyValues
abbrev exampleDynamics :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyDynamics
abbrev exampleInertia :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyInertia
abbrev exampleInitial :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyInitial
abbrev examplePackage :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyPackage

abbrev baseAuthority :=
  Cordis.GlobalPaperTraceBidirectionalNormalizer.Example.emptyAuthority

def emptyConfluent :
    ConfluentAuthority exampleValues exampleDynamics exampleInertia exampleInitial where
  base := baseAuthority
  rewrite := AuthorityStep baseAuthority
  selected := by
    intro source notNormal
    exact ⟨notNormal, rfl⟩
  decreases := by
    intro source target edge
    exact baseAuthority.decreases source edge.choose
  localJoin := by
    intro source left right leftStep _
    exact False.elim (leftStep.choose (by trivial))
  normal_iff := by
    intro source
    constructor
    · exact normal_irreducible baseAuthority
    · intro irreducible
      by_cases normal : baseAuthority.normal source
      · exact normal
      · exact False.elim (irreducible _ ⟨normal, rfl⟩)

theorem empty_normalizer_unique
    (left right : Cordis.GlobalPaperTraceBidirectionalNormalizer.Result
      emptyConfluent.base examplePackage)
    (leftEquality : Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize
      emptyConfluent.base examplePackage = some left)
    (rightEquality : Cordis.GlobalPaperTraceBidirectionalNormalizer.normalize
      emptyConfluent.base examplePackage = some right) :
    left.final = right.final :=
  normalize_results_unique emptyConfluent examplePackage left right leftEquality rightEquality

end Example

end
end Cordis.GlobalPaperTraceBidirectionalConfluence
