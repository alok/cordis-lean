import Cordis.GlobalPaperTraceNormalization
import Cordis.GlobalPaperTraceBackwardNormalization

/-!
# Bidirectional paper-trace certificate chains

This module gives one chain API for both orientations of the relation-aware adjacent rewrite.
Forward links prove source-to-target birth-erased relatedness; backward links prove the opposite
local relation and are symmetrized at the wrapper boundary.  The wrapper copies only the source
and target packages and derives all relation, assignment, rule, and actor facts from the selected
certificate, so an orientation cannot smuggle in an unrelated endpoint or assignment.

The resulting chain is still a finite supplied certificate.  It does not derive a normalizer,
canonical form, termination, confluence, lifecycle simulation, Lemma 72, or Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceBidirectionalNormalization

noncomputable section

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

structure TracePackage
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  final : State catalog Ambient
  trace : GlobalCalculus.Trace dynamics inertia initial final
  assignment : TraceProgramAssignment dynamics inertia trace

def ForwardPackage
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (package : Cordis.GlobalPaperTraceNormalization.TracePackage
      values dynamics inertia initial) :
    TracePackage values dynamics inertia initial := {
  final := package.final
  trace := package.trace
  assignment := package.assignment
}

def BackwardPackage
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (package : Cordis.GlobalPaperTraceBackwardNormalization.TracePackage
      values dynamics inertia initial) :
    TracePackage values dynamics inertia initial := {
  final := package.final
  trace := package.trace
  assignment := package.assignment
}

inductive BidirectionalWitness
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  | forward : Cordis.GlobalPaperTraceNormalization.AnyRewriteWitness
      values dynamics inertia initial →
      BidirectionalWitness values dynamics inertia initial
  | backward : Cordis.GlobalPaperTraceBackwardNormalization.AnyRewriteWitness
      values dynamics inertia initial →
      BidirectionalWitness values dynamics inertia initial

def BidirectionalWitness.source
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (witness : BidirectionalWitness values dynamics inertia initial) :
    TracePackage values dynamics inertia initial :=
  match witness with
  | .forward witness => ForwardPackage witness.source
  | .backward witness => BackwardPackage witness.source

def BidirectionalWitness.target
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (witness : BidirectionalWitness values dynamics inertia initial) :
    TracePackage values dynamics inertia initial :=
  match witness with
  | .forward witness =>
      ForwardPackage (witness.target dynamics inertia initial)
  | .backward witness =>
      BackwardPackage (witness.target dynamics inertia initial)

theorem BidirectionalWitness.source_related_target
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (witness : BidirectionalWitness values dynamics inertia initial) :
    BirthErasedRuleRelated values
      (witness.source.final) (witness.target dynamics inertia initial).final := by
  cases witness with
  | forward witness =>
      exact witness.result.final_related
  | backward witness =>
      exact birthErasedRuleRelated_symm witness.result.final_related

theorem BidirectionalWitness.target_rules_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (witness : BidirectionalWitness values dynamics inertia initial) :
    (witness.target dynamics inertia initial).trace.rules.Perm
      witness.source.trace.rules := by
  cases witness with
  | forward witness =>
      exact witness.result.rules_perm
  | backward witness =>
      exact witness.result.rules_perm

theorem BidirectionalWitness.target_actors_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (witness : BidirectionalWitness values dynamics inertia initial) :
    (witness.target dynamics inertia initial).trace.actors.Perm
      witness.source.trace.actors := by
  cases witness with
  | forward witness =>
      exact witness.result.actors_perm
  | backward witness =>
      exact witness.result.actors_perm

noncomputable def Connected
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (source : TracePackage values dynamics inertia initial) :
    List (BidirectionalWitness values dynamics inertia initial) → Prop
  | [] => True
  | link :: rest =>
      link.source = source ∧
        Connected (link.target dynamics inertia initial) rest

structure CertifiedChain
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  source : TracePackage values dynamics inertia initial
  links : List (BidirectionalWitness values dynamics inertia initial)
  connected : Connected source links

def CertifiedChain.terminal
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    List (BidirectionalWitness values dynamics inertia initial) →
      TracePackage values dynamics inertia initial
  | [] => source
  | link :: rest =>
      CertifiedChain.terminal dynamics inertia initial
        (link.target dynamics inertia initial) rest

theorem chain_final_related_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (BidirectionalWitness values dynamics inertia initial)),
      Connected source links →
        BirthErasedRuleRelated values source.final
          (CertifiedChain.terminal dynamics inertia initial source links).final
  | [], _ => birthErasedRuleRelated_refl values source.final
  | link :: rest, connected => by
      have tail := chain_final_related_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [CertifiedChain.terminal]
      rw [← connected.1]
      exact birthErasedRuleRelated_trans
        link.source_related_target tail

theorem chain_final_related
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : CertifiedChain values dynamics inertia initial) :
    BirthErasedRuleRelated values chain.source.final
      (CertifiedChain.terminal dynamics inertia initial chain.source chain.links).final :=
  chain_final_related_aux dynamics inertia initial chain.source chain.links chain.connected

theorem chain_rules_perm_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (BidirectionalWitness values dynamics inertia initial)),
      Connected source links →
        (CertifiedChain.terminal dynamics inertia initial source links).trace.rules.Perm
          source.trace.rules
  | [], _ => List.Perm.refl _
  | link :: rest, connected => by
      have tail := chain_rules_perm_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [CertifiedChain.terminal]
      rw [← connected.1]
      have tail' :
          (CertifiedChain.terminal dynamics inertia initial
            (link.target dynamics inertia initial) rest).trace.rules.Perm
            (link.target dynamics inertia initial).trace.rules := by
        simpa using tail
      exact tail'.trans link.target_rules_perm

theorem chain_rules_perm
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : CertifiedChain values dynamics inertia initial) :
    (CertifiedChain.terminal dynamics inertia initial chain.source chain.links).trace.rules.Perm
      chain.source.trace.rules :=
  chain_rules_perm_aux dynamics inertia initial chain.source chain.links chain.connected

theorem chain_actors_perm_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (BidirectionalWitness values dynamics inertia initial)),
      Connected source links →
        (CertifiedChain.terminal dynamics inertia initial source links).trace.actors.Perm
          source.trace.actors
  | [], _ => List.Perm.refl _
  | link :: rest, connected => by
      have tail := chain_actors_perm_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [CertifiedChain.terminal]
      rw [← connected.1]
      have tail' :
          (CertifiedChain.terminal dynamics inertia initial
            (link.target dynamics inertia initial) rest).trace.actors.Perm
            (link.target dynamics inertia initial).trace.actors := by
        simpa using tail
      exact tail'.trans link.target_actors_perm

theorem chain_actors_perm
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : CertifiedChain values dynamics inertia initial) :
    (CertifiedChain.terminal dynamics inertia initial chain.source chain.links).trace.actors.Perm
      chain.source.trace.actors :=
  chain_actors_perm_aux dynamics inertia initial chain.source chain.links chain.connected

/-! ## Two orientation-specific concrete packages over the same birth-gap fixture -/

namespace Example

open Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite
open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap
open Cordis.GlobalPaperRelation.BirthGap

abbrev values := exactValues
abbrev ExampleSignature :=
  Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
abbrev ExampleCatalog :=
  Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
abbrev ExampleAmbient :=
  Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient
abbrev ExampleSource :=
  Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source

noncomputable def sourcePackage
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    TracePackage values dynamics inertia ExampleSource where
  final := sourceFinal
  trace := sourceTrace dynamics inertia
  assignment := (assignedOccurrence dynamics inertia).sourceAssignment

noncomputable def forwardWitness
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    BidirectionalWitness values dynamics inertia ExampleSource :=
  .forward {
    source := {
      final := sourceFinal
      trace := sourceTrace dynamics inertia
      assignment := (assignedOccurrence dynamics inertia).sourceAssignment
    }
    occurrence := occurrence dynamics inertia
    assigned := assignedOccurrence dynamics inertia
    assigned_eq := rfl
    swap := swap dynamics inertia
    result := Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.result
      dynamics inertia
  }

noncomputable def backwardWitness
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    BidirectionalWitness values dynamics inertia ExampleSource :=
  .backward {
    source := {
      final := sourceFinal
      trace := sourceTrace dynamics inertia
      assignment := (assignedOccurrence dynamics inertia).sourceAssignment
    }
    occurrence := occurrence dynamics inertia
    assigned := assignedOccurrence dynamics inertia
    assigned_eq := rfl
    swap := swap dynamics inertia
    result := Cordis.GlobalPaperTraceBackwardRewrite.Example.result
      dynamics inertia
  }

noncomputable def forwardChain
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    CertifiedChain values dynamics inertia ExampleSource := {
  source := sourcePackage dynamics inertia
  links := [forwardWitness dynamics inertia]
  connected := by
    simp only [Connected]
    constructor
    · rfl
    · trivial
}

noncomputable def backwardChain
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    CertifiedChain values dynamics inertia ExampleSource := {
  source := sourcePackage dynamics inertia
  links := [backwardWitness dynamics inertia]
  connected := by
    simp only [Connected]
    constructor
    · rfl
    · trivial
}

theorem forward_final_related
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated values
      (forwardChain dynamics inertia).source.final
      (CertifiedChain.terminal dynamics inertia ExampleSource
        (forwardChain dynamics inertia).source (forwardChain dynamics inertia).links).final :=
  chain_final_related dynamics inertia ExampleSource (forwardChain dynamics inertia)

theorem backward_final_related
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated values
      (backwardChain dynamics inertia).source.final
      (CertifiedChain.terminal dynamics inertia ExampleSource
        (backwardChain dynamics inertia).source (backwardChain dynamics inertia).links).final :=
  chain_final_related dynamics inertia ExampleSource (backwardChain dynamics inertia)

theorem forward_rules_perm
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    (CertifiedChain.terminal dynamics inertia ExampleSource
      (forwardChain dynamics inertia).source (forwardChain dynamics inertia).links).trace.rules.Perm
      (forwardChain dynamics inertia).source.trace.rules :=
  chain_rules_perm dynamics inertia ExampleSource (forwardChain dynamics inertia)

theorem backward_rules_perm
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    (CertifiedChain.terminal dynamics inertia ExampleSource
      (backwardChain dynamics inertia).source
      (backwardChain dynamics inertia).links).trace.rules.Perm
      (backwardChain dynamics inertia).source.trace.rules :=
  chain_rules_perm dynamics inertia ExampleSource (backwardChain dynamics inertia)

def executableOrientationNames : List String := ["forward", "backward"]

def executableLinkCounts : List Nat := [1, 1]

theorem executableLinkCounts_eq : executableLinkCounts = [1, 1] := rfl

end Example

end
end Cordis.GlobalPaperTraceBidirectionalNormalization
