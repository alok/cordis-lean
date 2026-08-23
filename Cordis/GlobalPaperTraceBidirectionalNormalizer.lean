import Cordis.GlobalPaperTraceBidirectionalNormalization

/-!
# Conditional normalization over bidirectional paper-trace certificates

This module lifts the existing fuel-bounded normalizer shape to the unified forward/backward
certificate chain.  A caller supplies a normal-form predicate, a decidability proof, a decreasing
measure, and one orientation-indexed link at every non-normal package.  The resulting finite
trace retains its dependent assignment, endpoint relation, and rule/actor permutations.

The authority is intentionally explicit.  The CORDIS dynamics do not derive a rewrite strategy,
normal-form predicate, decreasing measure, termination theorem, confluence, Lemma 72, or Theorem
73; this module proves only the conditional finite bridge.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceBidirectionalNormalizer

noncomputable section

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceBidirectionalNormalization

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
variable {values : ValueSetoids sig}
variable {dynamics : Dynamics sig catalog Ambient}
variable {inertia : InertiaPolicy dynamics}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

abbrev Package
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) :=
  TracePackage values dynamics inertia initial

abbrev Link
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) :=
  BidirectionalWitness values dynamics inertia initial

abbrev InitialState := State catalog Ambient

variable {initial : InitialState}

structure Authority
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : InitialState) where
  measure : Package values dynamics inertia initial → Nat
  normal : Package values dynamics inertia initial → Prop
  normalDecidable : ∀ package, Decidable (normal package)
  step : ∀ (package : Package values dynamics inertia initial),
    ¬ normal package → { link : Link values dynamics inertia initial // link.source = package }
  decreases : ∀ (package : Package values dynamics inertia initial)
    (notNormal : ¬ normal package),
    measure ((step package notNormal).val.target dynamics inertia initial) < measure package

structure Result
    (authority : Authority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) where
  final : Package values dynamics inertia initial
  links : List (Link values dynamics inertia initial)
  connected : Connected source links
  terminal_eq :
    CertifiedChain.terminal dynamics inertia initial source links = final
  normal : authority.normal final

noncomputable def normalizeFuel
    (authority : Authority values dynamics inertia initial)
    (fuel : Nat)
    (source : Package values dynamics inertia initial) :
    Option (Result authority source) :=
  letI := authority.normalDecidable source
  match fuel with
  | 0 =>
      if h : authority.normal source then
        some {
          final := source
          links := []
          connected := trivial
          terminal_eq := rfl
          normal := h
        }
      else
        none
  | fuel + 1 =>
      if h : authority.normal source then
        some {
          final := source
          links := []
          connected := trivial
          terminal_eq := rfl
          normal := h
        }
      else
        let chosen := authority.step source h
        match normalizeFuel authority fuel chosen.val.target with
        | none => none
        | some tail =>
            some {
              final := tail.final
              links := chosen.val :: tail.links
              connected := ⟨chosen.property, tail.connected⟩
              terminal_eq := tail.terminal_eq
              normal := tail.normal
            }
termination_by fuel

noncomputable def normalize
    (authority : Authority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) :
    Option (Result authority source) :=
  normalizeFuel authority (authority.measure source) source

theorem normalizeFuel_some_of_measure_le
    (authority : Authority values dynamics inertia initial) :
    ∀ (fuel : Nat) (source : Package values dynamics inertia initial),
      authority.measure source ≤ fuel →
        ∃ result, normalizeFuel authority fuel source = some result
  | 0, source, bound => by
      by_cases h : authority.normal source
      · refine ⟨{
          final := source
          links := []
          connected := trivial
          terminal_eq := rfl
          normal := h
        }, ?_⟩
        simp [normalizeFuel, h]
      · have measure_zero : authority.measure source = 0 := Nat.eq_zero_of_le_zero bound
        have decrease := authority.decreases source h
        have impossible : authority.measure
            ((authority.step source h).val.target dynamics inertia initial) < 0 := by
          omega
        exact False.elim (Nat.not_lt_zero _ impossible)
  | fuel + 1, source, bound => by
      by_cases h : authority.normal source
      · refine ⟨{
          final := source
          links := []
          connected := trivial
          terminal_eq := rfl
          normal := h
        }, ?_⟩
        simp [normalizeFuel, h]
      · let chosen := authority.step source h
        have decrease := authority.decreases source h
        have targetBound :
            authority.measure (chosen.val.target dynamics inertia initial) ≤ fuel := by
          dsimp [chosen] at decrease ⊢
          omega
        obtain ⟨tail, tailEq⟩ := normalizeFuel_some_of_measure_le authority fuel
          (chosen.val.target dynamics inertia initial) targetBound
        refine ⟨{
          final := tail.final
          links := chosen.val :: tail.links
          connected := ⟨chosen.property, tail.connected⟩
          terminal_eq := tail.terminal_eq
          normal := tail.normal
        }, ?_⟩
        simp [normalizeFuel, h, chosen, tailEq]

theorem normalize_some
    (authority : Authority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) :
    ∃ result, normalize authority source = some result := by
  exact normalizeFuel_some_of_measure_le authority (authority.measure source)
    source (Nat.le_refl _)

def Result.chain
    {authority : Authority values dynamics inertia initial}
    {source : Package values dynamics inertia initial}
    (result : Result authority source) :
    CertifiedChain values dynamics inertia initial where
  source := source
  links := result.links
  connected := result.connected

theorem Result.terminal
    {authority : Authority values dynamics inertia initial}
    {source : Package values dynamics inertia initial}
    (result : Result authority source) :
    CertifiedChain.terminal dynamics inertia initial source result.links = result.final :=
  result.terminal_eq

theorem Result.final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {authority : Authority values dynamics inertia initial}
    {source : Package values dynamics inertia initial}
    (result : Result authority source) :
    BirthErasedRuleRelated values source.final result.final.final := by
  rw [← result.terminal_eq]
  exact chain_final_related dynamics inertia initial result.chain

theorem Result.rules_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {authority : Authority values dynamics inertia initial}
    {source : Package values dynamics inertia initial}
    (result : Result authority source) :
    result.final.trace.rules.Perm source.trace.rules := by
  rw [← result.terminal_eq]
  exact chain_rules_perm dynamics inertia initial result.chain

theorem Result.actors_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {authority : Authority values dynamics inertia initial}
    {source : Package values dynamics inertia initial}
    (result : Result authority source) :
    result.final.trace.actors.Perm source.trace.actors := by
  rw [← result.terminal_eq]
  exact chain_actors_perm dynamics inertia initial result.chain

namespace Example

open Cordis.GlobalPaperTraceBidirectionalNormalization.Example

/-! A fully executable empty authority checks the recursive bridge without pretending that CORDIS
itself supplies a strategy.  The nonempty forward/backward fixtures live in the chain module. -/

abbrev emptyValues := Cordis.GlobalPaperTraceBidirectionalNormalization.Example.values
abbrev emptyDynamics := Cordis.GlobalDeletion.Positive.dynamics
abbrev emptyInertia := Cordis.GlobalDeletion.Positive.inertia
abbrev emptyInitial := Cordis.GlobalDeletion.Positive.retired

def emptyPackage : Package emptyValues emptyDynamics emptyInertia emptyInitial := {
  final := emptyInitial
  trace := .nil emptyInitial
  assignment := .nil _
}

def emptyAuthority : Authority emptyValues emptyDynamics emptyInertia emptyInitial where
  measure _ := 0
  normal _ := True
  normalDecidable _ := inferInstance
  step _package notNormal := False.elim (notNormal trivial)
  decreases _package notNormal := False.elim (notNormal trivial)

def executableFuel : Nat := emptyAuthority.measure emptyPackage

theorem executableFuel_eq : executableFuel = 0 := rfl

theorem empty_normalizes :
    ∃ result, normalize emptyAuthority emptyPackage = some result :=
  normalize_some emptyAuthority emptyPackage

theorem empty_normal_form :
    ∀ result, normalize emptyAuthority emptyPackage = some result →
      emptyAuthority.normal result.final := by
  intro result _
  exact result.normal

end Example

end
end Cordis.GlobalPaperTraceBidirectionalNormalizer
