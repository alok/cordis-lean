import Cordis.GlobalPaperTraceBackwardRewrite

/-!
# Backward relation-aware rewrite chains

This module composes the backward adjacent-rewrite certificates from
`GlobalPaperTraceBackwardRewrite`.  A link consumes a dependent source package and produces a
shadow package whose final state is birth-erased related *to* the source final state.  The
orientation is therefore explicit in the chain theorem: the terminal endpoint is related back to
the original endpoint.  Assignments are reconstructed at every link and are never assumed as an
independent output.

This is finite certificate composition only.  It does not derive a rewrite strategy, a canonical
normal form, termination, confluence, lifecycle simulation, Lemma 72, or Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceBackwardNormalization

noncomputable section

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation
open Cordis.GlobalPaperTraceBackwardRewrite

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

abbrev GTrace
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial final : State catalog Ambient) :=
  Cordis.GlobalCalculus.Trace dynamics inertia initial final

structure TracePackage
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  final : State catalog Ambient
  trace : GTrace dynamics inertia initial final
  assignment : TraceProgramAssignment dynamics inertia trace

structure AnyRewriteWitness
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  source : TracePackage values dynamics inertia initial
  occurrence : AdjacentOccurrence source.trace
  assigned : AssignedAdjacentOccurrence occurrence
  assigned_eq : assigned.sourceAssignment = source.assignment
  swap : RelatedAssignedAdjacentSwap values occurrence.pair
  result : BackwardRelatedAdjacentRewrite values occurrence swap

noncomputable def AnyRewriteWitness.target
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (witness : AnyRewriteWitness values dynamics inertia initial) :
    TracePackage values dynamics inertia initial where
  final := witness.result.suffixReplay.result.shadowAfter
  trace := witness.result.trace
  assignment := witness.result.assignment witness.assigned

abbrev ChainLink
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) :=
  AnyRewriteWitness values dynamics inertia initial

noncomputable def ChainConnected
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (source : TracePackage values dynamics inertia initial) :
    List (ChainLink values dynamics inertia initial) → Prop
  | [] => True
  | link :: rest =>
      link.source = source ∧
        ChainConnected (link.target dynamics inertia initial) rest

structure RewriteChain
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  source : TracePackage values dynamics inertia initial
  links : List (ChainLink values dynamics inertia initial)
  connected : ChainConnected source links

noncomputable def RewriteChain.single
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (witness : AnyRewriteWitness values dynamics inertia initial) :
    RewriteChain values dynamics inertia initial where
  source := witness.source
  links := [witness]
  connected := by
    simp [ChainConnected]

def RewriteChain.terminal
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    List (ChainLink values dynamics inertia initial) →
      TracePackage values dynamics inertia initial
  | [] => source
  | link :: rest =>
      RewriteChain.terminal dynamics inertia initial
        (link.target dynamics inertia initial) rest

theorem RewriteChain.single_terminal
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (witness : AnyRewriteWitness values dynamics inertia initial) :
    RewriteChain.terminal dynamics inertia initial witness.source
      (RewriteChain.single dynamics inertia initial witness).links =
        AnyRewriteWitness.target dynamics inertia initial witness := rfl

theorem chain_final_related_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (ChainLink values dynamics inertia initial)),
      ChainConnected source links →
        BirthErasedRuleRelated values
          (RewriteChain.terminal dynamics inertia initial source links).final
          source.final
  | [], _ => birthErasedRuleRelated_refl values source.final
  | link :: rest, connected => by
      have tail := chain_final_related_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [RewriteChain.terminal]
      rw [← connected.1]
      exact birthErasedRuleRelated_trans tail
        (by simpa [AnyRewriteWitness.target] using link.result.final_related)

theorem chain_final_related
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : RewriteChain values dynamics inertia initial) :
    BirthErasedRuleRelated values
      (RewriteChain.terminal dynamics inertia initial chain.source chain.links).final
      chain.source.final :=
  chain_final_related_aux dynamics inertia initial chain.source chain.links chain.connected

theorem chain_rules_perm_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (ChainLink values dynamics inertia initial)),
      ChainConnected source links →
        (RewriteChain.terminal dynamics inertia initial source links).trace.rules.Perm
          source.trace.rules
  | [], _ => List.Perm.refl _
  | link :: rest, connected => by
      have tail := chain_rules_perm_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [RewriteChain.terminal]
      rw [← connected.1]
      have tail' :
          (RewriteChain.terminal dynamics inertia initial
            (link.target dynamics inertia initial) rest).trace.rules.Perm
            link.result.trace.rules := by
        simpa [AnyRewriteWitness.target] using tail
      exact tail'.trans link.result.rules_perm

theorem chain_rules_perm
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : RewriteChain values dynamics inertia initial) :
    (RewriteChain.terminal dynamics inertia initial chain.source chain.links).trace.rules.Perm
      chain.source.trace.rules :=
  chain_rules_perm_aux dynamics inertia initial chain.source chain.links chain.connected

theorem chain_actors_perm_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial) :
    ∀ (links : List (ChainLink values dynamics inertia initial)),
      ChainConnected source links →
        (RewriteChain.terminal dynamics inertia initial source links).trace.actors.Perm
          source.trace.actors
  | [], _ => List.Perm.refl _
  | link :: rest, connected => by
      have tail := chain_actors_perm_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [RewriteChain.terminal]
      rw [← connected.1]
      have tail' :
          (RewriteChain.terminal dynamics inertia initial
            (link.target dynamics inertia initial) rest).trace.actors.Perm
            link.result.trace.actors := by
        simpa [AnyRewriteWitness.target] using tail
      exact tail'.trans link.result.actors_perm

theorem chain_actors_perm
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : RewriteChain values dynamics inertia initial) :
    (RewriteChain.terminal dynamics inertia initial chain.source chain.links).trace.actors.Perm
      chain.source.trace.actors :=
  chain_actors_perm_aux dynamics inertia initial chain.source chain.links chain.connected

/-! ## Concrete backward chain -/

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

noncomputable def sourcePackage
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    TracePackage values dynamics inertia
      Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source where
  final := sourceFinal
  trace := sourceTrace dynamics inertia
  assignment := (assignedOccurrence dynamics inertia).sourceAssignment

noncomputable def witness
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    AnyRewriteWitness values dynamics inertia
      Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source where
  source := sourcePackage dynamics inertia
  occurrence := occurrence dynamics inertia
  assigned := assignedOccurrence dynamics inertia
  assigned_eq := rfl
  swap := swap dynamics inertia
  result := Cordis.GlobalPaperTraceBackwardRewrite.Example.result dynamics inertia

noncomputable def chain
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    RewriteChain values dynamics inertia
      Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source :=
  RewriteChain.single dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (witness dynamics inertia)

noncomputable def terminal
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    TracePackage values dynamics inertia
      Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source :=
  RewriteChain.terminal dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (chain dynamics inertia).source (chain dynamics inertia).links

theorem terminal_eq_target
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    terminal dynamics inertia =
      AnyRewriteWitness.target dynamics inertia
        Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
        (witness dynamics inertia) := by
  unfold terminal chain
  exact RewriteChain.single_terminal dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (witness dynamics inertia)

theorem terminal_final_related
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated values (terminal dynamics inertia).final sourceFinal :=
  chain_final_related dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (chain dynamics inertia)

theorem terminal_wellFormed
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    WellFormed (terminal dynamics inertia).final := by
  rw [terminal_eq_target]
  exact Cordis.GlobalPaperTraceBackwardRewrite.Example.final_wellFormed
    dynamics inertia

theorem terminal_assignment_exists
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    Nonempty (TraceProgramAssignment dynamics inertia (terminal dynamics inertia).trace) :=
  ⟨(terminal dynamics inertia).assignment⟩

theorem terminal_rules_perm
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    (terminal dynamics inertia).trace.rules.Perm (sourceTrace dynamics inertia).rules :=
  chain_rules_perm dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (chain dynamics inertia)

theorem terminal_actors_perm
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    (terminal dynamics inertia).trace.actors.Perm (sourceTrace dynamics inertia).actors :=
  chain_actors_perm dynamics inertia
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.Source
    (chain dynamics inertia)

def executableLinkCount : Nat := 1

theorem executableLinkCount_eq
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    executableLinkCount = (chain dynamics inertia).links.length := by
  rfl

def executableActorNames : List Signature.Name := [2, 1, 1]

theorem executableActorNames_eq
    (dynamics : Dynamics ExampleSignature ExampleCatalog ExampleAmbient)
    (inertia : InertiaPolicy dynamics) :
    executableActorNames =
      (terminal dynamics inertia).trace.actors.map (fun actor => match actor with
        | .fiber name => name) := by
  rw [terminal_eq_target]
  exact (Cordis.GlobalPaperTraceBackwardRewrite.Example.backward_actors
    dynamics inertia).symm

end Example

end
end Cordis.GlobalPaperTraceBackwardNormalization
