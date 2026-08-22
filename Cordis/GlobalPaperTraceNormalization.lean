import Cordis.GlobalPaperTraceDeletion

/-!
# Finite certificate-driven paper-trace rewrite chains

This module packages a finite chain of already-certified birth-erased adjacent rewrites.
Each link retains its source assignment, its assigned adjacent occurrence, and the
`RelatedAdjacentRewrite` certificate that constructs the complete rewritten trace and its
transported assignment.  The chain therefore proves final birth-erased relatedness and
permutation of detailed rules and actors.

This is a normalization *certificate* layer, not an automatic normalizer.  No strategy,
normal-form existence or uniqueness, termination, confluence, full episode deletion, or
paper Lemma 72/Theorem 73 is claimed.  In particular, a caller must supply every rewrite
link and its connectivity proof.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceNormalization

noncomputable section

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations
open Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation

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
  result : RelatedAdjacentRewrite values occurrence swap

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
    (source : TracePackage values dynamics inertia initial)
    : List (ChainLink values dynamics inertia initial) →
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
    (source : TracePackage values dynamics inertia initial)
    : ∀ (links : List (ChainLink values dynamics inertia initial)),
      ChainConnected source links →
        BirthErasedRuleRelated values source.final
          (RewriteChain.terminal dynamics inertia initial source links).final
  | [], _ => birthErasedRuleRelated_refl values source.final
  | link :: rest, connected => by
      have tail := chain_final_related_aux dynamics inertia initial
        (link.target dynamics inertia initial) rest connected.2
      simp only [RewriteChain.terminal]
      rw [← connected.1]
      exact birthErasedRuleRelated_trans link.result.final_related
        (by simpa [AnyRewriteWitness.target] using tail)

theorem chain_final_related
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (chain : RewriteChain values dynamics inertia initial) :
    BirthErasedRuleRelated values chain.source.final
      (RewriteChain.terminal dynamics inertia initial chain.source chain.links).final :=
  chain_final_related_aux dynamics inertia initial chain.source chain.links chain.connected

theorem chain_rules_perm_aux
    {values : ValueSetoids sig}
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (source : TracePackage values dynamics inertia initial)
    : ∀ (links : List (ChainLink values dynamics inertia initial)),
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
    (source : TracePackage values dynamics inertia initial)
    : ∀ (links : List (ChainLink values dynamics inertia initial)),
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

theorem detailedRule_eq_insert_of_rule_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (rule_eq : step.rule = .oInsert) :
    detailedRule step = .orchestration .insert := by
  cases step with
  | orchestration step =>
      cases step <;> simp_all [detailedRule, GlobalVestigial.orchestrationKind,
        GlobalNameLifecycle.globalRuleOfOrchestrationKind]
  | lifecycle transition =>
      cases transition <;> simp_all [Transition.rule,
        GlobalNameLifecycle.globalRuleOfLifecycleRule]

theorem detailedRule_eq_begin_of_rule_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (rule_eq : step.rule = .lBegin) :
    detailedRule step = .lifecycle .begin := by
  cases step with
  | orchestration step =>
      cases step <;> simp_all [GlobalVestigial.orchestrationKind,
        GlobalNameLifecycle.globalRuleOfOrchestrationKind]
  | lifecycle transition =>
      cases transition <;> simp_all [detailedRule, Transition.rule,
        GlobalNameLifecycle.globalRuleOfLifecycleRule]

namespace Example

open Cordis.GlobalDeletion.Positive

abbrev values := Cordis.GlobalPaperRelation.DirectedReplayExample.values
abbrev dynamics := Cordis.GlobalDeletion.Positive.dynamics
abbrev inertia := Cordis.GlobalDeletion.Positive.inertia
abbrev initial := Cordis.GlobalDeletion.Positive.retired

def emptyPackage : TracePackage values dynamics inertia initial where
  final := initial
  trace := .nil initial
  assignment := .nil _

def emptyChain : RewriteChain values dynamics inertia initial where
  source := emptyPackage
  links := []
  connected := trivial

def executableLinkCount : Nat := emptyChain.links.length

def emptyTerminal : TracePackage values dynamics inertia initial :=
  RewriteChain.terminal dynamics inertia initial emptyChain.source emptyChain.links

theorem empty_chain_terminal :
    emptyTerminal = emptyPackage := rfl

theorem empty_chain_related :
    BirthErasedRuleRelated values emptyChain.source.final emptyTerminal.final :=
  chain_final_related dynamics inertia initial emptyChain

theorem empty_chain_rules :
    emptyTerminal.trace.rules.Perm emptyChain.source.trace.rules :=
  chain_rules_perm dynamics inertia initial emptyChain

theorem empty_chain_actors :
    emptyTerminal.trace.actors.Perm emptyChain.source.trace.actors :=
  chain_actors_perm dynamics inertia initial emptyChain

/-! ## A nonempty executable activation/orchestration link -/

namespace ActivationOrchestration

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap

abbrev values :=
  Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.exactValues
abbrev dynamics := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.dynamics
abbrev inertia := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.inertia
abbrev initial := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.initial
abbrev final :=
  Cordis.GlobalActivationOrchestrationTransposition.BeginInsert.final
abbrev sourceTrace := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.sourceTrace
abbrev sourceAssignment :=
  Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.sourceAssignment
abbrev occurrence := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.occurrence
abbrev assigned := Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.assignedOccurrence

theorem final_wellFormed : WellFormed final := by
  apply (Cordis.GlobalActivationOrchestrationTransposition.BeginInsert.normal).preservesWellFormed
  rw [Cordis.GlobalActivationOrchestrationTransposition.BeginInsert.activation_after]
  exact Cordis.GlobalLifecycle.Example.beginState_wellFormed

noncomputable def exactSwap :
    AssignedAdjacentSwap occurrence.pair :=
  Cordis.GlobalTraceRewrite.Example.ActivationOrchestration.ledgerAssignedSwap

noncomputable def swap : RelatedAssignedAdjacentSwap values occurrence.pair :=
  RelatedAssignedAdjacentSwap.ofExact exactSwap
    (by
      exact detailedRule_eq_insert_of_rule_eq (by
        calc
          exactSwap.swapped.first.rule = occurrence.pair.second.rule :=
            exactSwap.first_rule
          _ = .oInsert := rfl))
    (by
      exact detailedRule_eq_begin_of_rule_eq (by
        calc
          exactSwap.swapped.second.rule = occurrence.pair.first.rule :=
            exactSwap.second_rule
          _ = .lBegin := rfl))

noncomputable def suffixReplay :
    ForwardPaperTraceReplay values occurrence.afterTrace swap.swappedAfter where
  result := {
    shadowAfter := final
    shadow := .nil final
    certificate := .nil (birthErasedRuleRelated_refl values final)
  }
  sourceAfter_wellFormed := final_wellFormed
  shadowAfter_wellFormed := final_wellFormed
  detailedRules_eq := by rfl

noncomputable def rewrite : RelatedAdjacentRewrite values occurrence swap where
  suffixReplay := suffixReplay

noncomputable def witness : AnyRewriteWitness values dynamics inertia initial where
  source := {
    final := final
    trace := sourceTrace
    assignment := sourceAssignment
  }
  occurrence := occurrence
  assigned := assigned
  assigned_eq := rfl
  swap := swap
  result := rewrite

noncomputable def chain : RewriteChain values dynamics inertia initial :=
  RewriteChain.single dynamics inertia initial witness

def executableLinkCount : Nat := 1

theorem chain_links_length : chain.links.length = 1 := by
  rfl

theorem executableLinkCount_eq : executableLinkCount = chain.links.length := by
  rw [chain_links_length]
  rfl

noncomputable def terminal : TracePackage values dynamics inertia initial :=
  RewriteChain.terminal dynamics inertia initial chain.source chain.links

theorem terminal_eq_target :
    terminal = AnyRewriteWitness.target dynamics inertia initial witness := by
  unfold terminal chain
  exact RewriteChain.single_terminal dynamics inertia initial witness

theorem terminal_rules :
    terminal.trace.rules = [.oInsert, .oInsert, .lBegin] := by
  rw [terminal_eq_target]
  change rewrite.trace.rules = _
  rw [RelatedAdjacentRewrite.trace, GlobalTraceRewrite.Trace.rules_append]
  simp only [GlobalCalculus.Trace.rules]
  rw [swap.first_rule, swap.second_rule]
  rfl

theorem terminal_actors :
    terminal.trace.actors = [.fiber 0, .fiber 1, .fiber 0] := by
  rw [terminal_eq_target]
  change rewrite.trace.actors = _
  rw [RelatedAdjacentRewrite.trace, GlobalTraceRewrite.Trace.actors_append]
  simp only [GlobalCalculus.Trace.actors]
  rw [swap.first_actor, swap.second_actor]
  rfl

theorem terminal_final_related :
    BirthErasedRuleRelated values chain.source.final terminal.final :=
  chain_final_related dynamics inertia initial chain

theorem terminal_rules_perm :
    terminal.trace.rules.Perm chain.source.trace.rules :=
  chain_rules_perm dynamics inertia initial chain

theorem terminal_actors_perm :
    terminal.trace.actors.Perm chain.source.trace.actors :=
  chain_actors_perm dynamics inertia initial chain

def executableProjection : List Cordis.GlobalCalculus.Rule × List Nat :=
  ([.oInsert, .oInsert, .lBegin], [0, 1, 0])

theorem terminal_projection :
    (terminal.trace.rules, terminal.trace.actors.map (fun actor ↦ match actor with
      | .fiber name => name)) = executableProjection := by
  rw [terminal_rules, terminal_actors]
  rfl

def executableTerminalRules : List Cordis.GlobalCalculus.Rule :=
  [.oInsert, .oInsert, .lBegin]

def executableTerminalActors : List Nat := [0, 1, 0]

theorem executableTerminalRules_eq :
    executableTerminalRules = [.oInsert, .oInsert, .lBegin] := rfl

theorem executableTerminalActors_eq : executableTerminalActors = [0, 1, 0] := rfl

/-! ## A connected two-link cycle

The first link above is deliberately non-reflexive: it moves the Begin occurrence across the
following orchestration step.  The reverse link is reconstructed from the moved pair and its
transported assignment ledger.  This gives a small but genuinely recursive chain witness: the
second link consumes the first link's target package, rather than merely repeating the empty-chain
or one-link surface.
-/

noncomputable def targetTrace :
    GlobalCalculus.Trace dynamics inertia initial final :=
  witness.result.trace

noncomputable def targetOccurrence : AdjacentOccurrence targetTrace where
  windowStart := occurrence.windowStart
  windowEnd := occurrence.windowEnd
  beforeTrace := occurrence.beforeTrace
  pair := swap.swapped
  afterTrace := .nil final
  decomposition := by
    rfl

noncomputable def reverseExact : AssignedAdjacentSwap targetOccurrence.pair where
  toExactAdjacentSwap := {
    swapped := occurrence.pair
    first_rule := (RelatedAssignedAdjacentSwap.second_rule swap).symm
    second_rule := (RelatedAssignedAdjacentSwap.first_rule swap).symm
    first_actor := swap.second_actor.symm
    second_actor := swap.first_actor.symm
  }
  swappedFirstAssignment := assigned.firstAssignment
  swappedSecondAssignment := assigned.secondAssignment

noncomputable def targetAssigned : AssignedAdjacentOccurrence targetOccurrence where
  beforeAssignment := assigned.beforeAssignment
  firstAssignment := swap.swappedFirstAssignment
  secondAssignment := swap.swappedSecondAssignment
  afterAssignment := .nil final

theorem targetAssigned_eq :
    targetAssigned.sourceAssignment = witness.result.assignment assigned := by
  rfl

noncomputable def reverseSwap :
    RelatedAssignedAdjacentSwap values targetOccurrence.pair := by
  let targetSecondDetailed : detailedRule targetOccurrence.pair.second =
      .lifecycle .begin := detailedRule_eq_begin_of_rule_eq (by
        calc
          targetOccurrence.pair.second.rule = occurrence.pair.first.rule :=
            RelatedAssignedAdjacentSwap.second_rule swap
          _ = .lBegin := rfl)
  let targetFirstDetailed : detailedRule targetOccurrence.pair.first =
      .orchestration .insert := detailedRule_eq_insert_of_rule_eq (by
        calc
          targetOccurrence.pair.first.rule = occurrence.pair.second.rule :=
            RelatedAssignedAdjacentSwap.first_rule swap
          _ = .oInsert := rfl)
  exact RelatedAssignedAdjacentSwap.ofExact reverseExact
    ((detailedRule_eq_begin_of_rule_eq (by
      calc
        reverseExact.toExactAdjacentSwap.swapped.first.rule =
            targetOccurrence.pair.second.rule := reverseExact.first_rule
        _ = occurrence.pair.first.rule := RelatedAssignedAdjacentSwap.second_rule swap
        _ = .lBegin := rfl)).trans targetSecondDetailed.symm)
    ((detailedRule_eq_insert_of_rule_eq (by
      calc
        reverseExact.toExactAdjacentSwap.swapped.second.rule =
            targetOccurrence.pair.first.rule := reverseExact.second_rule
        _ = occurrence.pair.second.rule := RelatedAssignedAdjacentSwap.first_rule swap
        _ = .oInsert := rfl)).trans targetFirstDetailed.symm)

noncomputable def reverseSuffixReplay :
    ForwardPaperTraceReplay values targetOccurrence.afterTrace reverseSwap.swappedAfter where
  result := {
    shadowAfter := final
    shadow := .nil final
    certificate := .nil (birthErasedRuleRelated_refl values final)
  }
  sourceAfter_wellFormed := final_wellFormed
  shadowAfter_wellFormed := final_wellFormed
  detailedRules_eq := by rfl

noncomputable def reverseRewrite :
    RelatedAdjacentRewrite values targetOccurrence reverseSwap where
  suffixReplay := reverseSuffixReplay

noncomputable def reverseWitness :
    AnyRewriteWitness values dynamics inertia initial where
  source := witness.target dynamics inertia initial
  occurrence := targetOccurrence
  assigned := targetAssigned
  assigned_eq := targetAssigned_eq
  swap := reverseSwap
  result := reverseRewrite

noncomputable def twoChain : RewriteChain values dynamics inertia initial where
  source := witness.source
  links := [witness, reverseWitness]
  connected := by
    constructor
    · rfl
    · constructor
      · rfl
      · trivial

def executableTwoLinkCount : Nat := 2

theorem executableTwoLinkCount_eq : executableTwoLinkCount = twoChain.links.length := by
  rfl

noncomputable def twoChainTerminal : TracePackage values dynamics inertia initial :=
  RewriteChain.terminal dynamics inertia initial twoChain.source twoChain.links

theorem twoChain_terminal_eq_source : twoChainTerminal = witness.source := by
  unfold twoChainTerminal twoChain
  rfl

theorem twoChain_terminal_rules :
    twoChainTerminal.trace.rules = [.oInsert, .lBegin, .oInsert] := by
  rw [twoChain_terminal_eq_source]
  rfl

theorem twoChain_terminal_actors :
    twoChainTerminal.trace.actors = [.fiber 0, .fiber 0, .fiber 1] := by
  rw [twoChain_terminal_eq_source]
  rfl

theorem twoChain_terminal_final_related :
    BirthErasedRuleRelated values twoChain.source.final twoChainTerminal.final := by
  exact chain_final_related dynamics inertia initial twoChain

theorem twoChain_terminal_rules_perm :
    twoChainTerminal.trace.rules.Perm twoChain.source.trace.rules := by
  exact chain_rules_perm dynamics inertia initial twoChain

theorem twoChain_terminal_actors_perm :
    twoChainTerminal.trace.actors.Perm twoChain.source.trace.actors := by
  exact chain_actors_perm dynamics inertia initial twoChain

/-! These projections keep the executable test surface independent of the
noncomputable proof-carrying terminal package above. -/

def executableTwoLinkTerminalRules : List GlobalCalculus.Rule :=
  [.oInsert, .lBegin, .oInsert]

def executableTwoLinkTerminalActors : List Nat := [0, 0, 1]

theorem executableTwoLinkTerminalRules_eq :
    executableTwoLinkTerminalRules = twoChainTerminal.trace.rules := by
  rw [twoChain_terminal_rules]
  rfl

theorem executableTwoLinkTerminalActors_eq :
    executableTwoLinkTerminalActors =
      twoChainTerminal.trace.actors.map (fun actor => match actor with
        | .fiber name => name) := by
  rw [twoChain_terminal_actors]
  rfl

end ActivationOrchestration

end Example

end
end Cordis.GlobalPaperTraceNormalization
