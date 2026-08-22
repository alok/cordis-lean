import Cordis.GlobalPaperTraceConfluence

/-!
# Indexed proof-carrying trace normalization

The unscoped confluence bridge quantifies an authority over every `TracePackage`.  That is a
useful abstract theorem, but an actual rewrite strategy normally has a smaller reachable family.
This module makes that family a type: `IndexedAuthority.Node` is an explicit index, `package`
maps each index to its dependent trace package, and every selected link carries the exact source
and target package equations.  No reachability proposition is eliminated into data and no opaque
package equality is used to choose a link.

Fuel normalization, authority-path reconstruction, decreasing-system confluence, and uniqueness of
normal endpoints are proved for the indexed family.  The example is the existing nonempty
activation/orchestration swap from `GlobalPaperTraceNormalization`: its source and target are two
constructors of a finite index type, and the theorem exercises a real rewrite link, assignment,
rule projection, actor projection, and endpoint.

This remains a finite certificate layer.  It does not derive lifecycle simulation, a global paper
normalization strategy, Lemma 72, or Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceScopedConfluence

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalPaperTraceNormalization
open Cordis.GlobalPaperTraceConfluence
open Cordis.GlobalRelations Cordis.GlobalPaperRelation

universe u v

variable {Node : Type v}

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
  AnyRewriteWitness values dynamics inertia initial

structure StepChoice
    (Node : Type v)
    (package : Node → Package values dynamics inertia initial)
    (node : Node) where
  next : Node
  link : Link values dynamics inertia initial
  source_eq : link.source = package node
  target_eq : link.target dynamics inertia initial = package next

structure IndexedAuthority (Node : Type v) where
  package : Node → Package values dynamics inertia initial
  package_injective : Function.Injective package
  measure : Node → Nat
  normal : Node → Prop
  normalDecidable : ∀ node, Decidable (normal node)
  step : ∀ (node : Node), ¬ normal node → StepChoice Node package node
  decreases : ∀ (node : Node) (notNormal : ¬ normal node),
    measure (step node notNormal).next < measure node

structure Result
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node) where
  final : Node
  links : List (Link values dynamics inertia initial)
  connected : ChainConnected (authority.package source) links
  terminal_eq :
    RewriteChain.terminal dynamics inertia initial (authority.package source) links =
      authority.package final
  normal : authority.normal final

noncomputable def normalizeFuel
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (fuel : Nat) (source : Node) :
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
        match normalizeFuel authority fuel chosen.next with
        | none => none
        | some tail =>
            have tailConnected : ChainConnected chosen.link.target tail.links := by
              simpa [chosen.target_eq] using tail.connected
            some {
              final := tail.final
              links := chosen.link :: tail.links
              connected := ⟨chosen.source_eq, tailConnected⟩
              terminal_eq := by
                simpa [RewriteChain.terminal, chosen.target_eq] using tail.terminal_eq
              normal := tail.normal
            }
termination_by fuel

noncomputable def normalize
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node) : Option (Result authority source) :=
  normalizeFuel authority (authority.measure source) source

theorem normalizeFuel_some_of_measure_le
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node) :
    ∀ (fuel : Nat) (source : Node), authority.measure source ≤ fuel →
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
        have impossible : authority.measure (authority.step source h).next < 0 := by
          rw [measure_zero] at decrease
          exact decrease
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
        have targetBound : authority.measure chosen.next ≤ fuel := by
          dsimp [chosen] at decrease ⊢
          omega
        obtain ⟨tail, tailEq⟩ := normalizeFuel_some_of_measure_le authority fuel
          chosen.next targetBound
        have tailConnected : ChainConnected chosen.link.target tail.links := by
          simpa [chosen.target_eq] using tail.connected
        refine ⟨{
          final := tail.final
          links := chosen.link :: tail.links
          connected := ⟨chosen.source_eq, tailConnected⟩
          terminal_eq := by
            simpa [RewriteChain.terminal, chosen.target_eq] using tail.terminal_eq
          normal := tail.normal
        }, ?_⟩
        simp [normalizeFuel, h, chosen, tailEq]

def IndexedLinked
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node) : List (Link values dynamics inertia initial) → Prop
  | [] => authority.normal source
  | link :: rest =>
      ∃ notNormal : ¬ authority.normal source,
        link = (authority.step source notNormal).link ∧
          IndexedLinked authority (authority.step source notNormal).next rest

theorem normalizeFuel_indexedLinked
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node) :
    ∀ (fuel : Nat) (source : Node) (result : Result authority source),
      normalizeFuel authority fuel source = some result →
        IndexedLinked authority source result.links
  | 0, source, result, equality => by
      unfold normalizeFuel at equality
      split at equality
      · rename_i normal
        cases equality
        exact normal
      · contradiction
  | fuel + 1, source, result, equality => by
      unfold normalizeFuel at equality
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
          exact normalizeFuel_indexedLinked authority fuel chosen.next tail tailEquality

theorem normalize_indexedLinked
    (authority : IndexedAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node) (result : Result authority source)
    (equality : normalize authority source = some result) :
    IndexedLinked authority source result.links := by
  exact normalizeFuel_indexedLinked authority (authority.measure source) source result
    (by simpa [normalize] using equality)

structure ConfluentAuthority (Node : Type v) where
  base : IndexedAuthority (values := values) (dynamics := dynamics)
    (inertia := inertia) (initial := initial) Node
  rewrite : Node → Node → Prop
  selected : ∀ (source : Node) (notNormal : ¬ base.normal source),
    rewrite source (base.step source notNormal).next
  decreases : ∀ {source target : Node},
    rewrite source target → base.measure target < base.measure source
  localJoin : ∀ {source left right : Node},
    rewrite source left → rewrite source right → Joinable rewrite left right
  normal_iff : ∀ (source : Node),
    base.normal source ↔ Irreducible rewrite source

def authoritySystem (authority : ConfluentAuthority (values := values)
    (dynamics := dynamics) (inertia := inertia) (initial := initial) Node) :
    DecreasingSystem Node where
  step := authority.rewrite
  measure := authority.base.measure
  decreases := authority.decreases
  localJoin := authority.localJoin

theorem path_of_indexedLinked
    (authority : ConfluentAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node) :
    ∀ (links : List (Link values dynamics inertia initial)),
      ∀ {final : Node},
        IndexedLinked authority.base source links →
        RewriteChain.terminal dynamics inertia initial
            (authority.base.package source) links = authority.base.package final →
        Path authority.rewrite source final
  | [], final, evidence, terminal_eq => by
      have nodesEqual : source = final := authority.base.package_injective terminal_eq
      cases nodesEqual
      exact .refl _
  | link :: rest, final, evidence, terminal_eq => by
      obtain ⟨notNormal, linkEq, tailEvidence⟩ := evidence
      let chosen := authority.base.step source notNormal
      subst link
      have tailTerminalEq :
          RewriteChain.terminal dynamics inertia initial
              (authority.base.package chosen.next) rest = authority.base.package final := by
        change RewriteChain.terminal dynamics inertia initial
            (chosen.link.target dynamics inertia initial) rest = authority.base.package final
          at terminal_eq
        rw [chosen.target_eq] at terminal_eq
        exact terminal_eq
      have tailPath := path_of_indexedLinked authority chosen.next rest
        tailEvidence tailTerminalEq
      exact .cons (authority.selected source notNormal) tailPath

theorem normal_rewrite_irreducible
    (authority : ConfluentAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    {source : Node} (normal : authority.base.normal source) :
    Irreducible authority.rewrite source :=
  (authority.normal_iff source).mp normal

theorem normalize_results_unique
    (authority : ConfluentAuthority (values := values) (dynamics := dynamics)
      (inertia := inertia) (initial := initial) Node)
    (source : Node)
    (left right : Result authority.base source)
    (leftEquality : normalize authority.base source = some left)
    (rightEquality : normalize authority.base source = some right) :
    authority.base.package left.final = authority.base.package right.final := by
  have leftEvidence := normalize_indexedLinked authority.base source left leftEquality
  have rightEvidence := normalize_indexedLinked authority.base source right rightEquality
  have leftPath := path_of_indexedLinked authority source left.links
    leftEvidence left.terminal_eq
  have rightPath := path_of_indexedLinked authority source right.links
    rightEvidence right.terminal_eq
  exact congrArg (fun node => authority.base.package node)
    (NormalForm.endpoint_eq (authoritySystem authority)
      { endpoint := left.final
        path := leftPath
        irreducible := normal_rewrite_irreducible authority left.normal }
      { endpoint := right.final
        path := rightPath
        irreducible := normal_rewrite_irreducible authority right.normal })

/-! ## Nonempty activation/orchestration fixture -/

namespace Example

abbrev demoValues :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.values
abbrev demoDynamics :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.dynamics
abbrev demoInertia :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.inertia
abbrev demoInitial :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.initial
abbrev DemoPackage := Package demoValues demoDynamics demoInertia demoInitial

noncomputable def demoSource : DemoPackage :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.witness.source

noncomputable def demoTarget : DemoPackage :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.witness.target
    demoDynamics demoInertia demoInitial

noncomputable def demoLink : Link demoValues demoDynamics demoInertia demoInitial :=
  Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.witness

theorem demoLink_source : demoLink.source = demoSource := rfl

theorem demoLink_target :
    demoLink.target demoDynamics demoInertia demoInitial = demoTarget := rfl

theorem demoSource_rules :
    demoSource.trace.rules = [.oInsert, .lBegin, .oInsert] := rfl

theorem demoTarget_rules :
    demoTarget.trace.rules = [.oInsert, .oInsert, .lBegin] := by
  change (Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.witness.target
    demoDynamics demoInertia demoInitial).trace.rules = _
  rw [← Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.terminal_eq_target]
  exact Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.terminal_rules

theorem demoSource_ne_target : demoSource ≠ demoTarget := by
  intro equality
  have rulesEquality := congrArg (fun package : DemoPackage => package.trace.rules) equality
  rw [demoSource_rules, demoTarget_rules] at rulesEquality
  cases rulesEquality

inductive DemoNode where
  | source
  | target
deriving DecidableEq, Repr

noncomputable def demoPackage : DemoNode → DemoPackage
  | .source => demoSource
  | .target => demoTarget

theorem demoPackage_injective : Function.Injective demoPackage := by
  intro left right equality
  cases left <;> cases right
  · rfl
  · exact False.elim (demoSource_ne_target equality)
  · exact False.elim (demoSource_ne_target equality.symm)
  · rfl

noncomputable def demoAuthority : IndexedAuthority (Node := DemoNode)
    (values := demoValues) (dynamics := demoDynamics)
    (inertia := demoInertia) (initial := demoInitial) where
  package := demoPackage
  package_injective := demoPackage_injective
  measure
    | .source => 1
    | .target => 0
  normal
    | .source => False
    | .target => True
  normalDecidable
    | .source => inferInstance
    | .target => inferInstance
  step node notNormal := by
    cases node with
    | source =>
        exact {
          next := .target
          link := demoLink
          source_eq := demoLink_source
          target_eq := demoLink_target
        }
    | target =>
        change ¬ True at notNormal
        exact False.elim (notNormal True.intro)
  decreases node notNormal := by
    cases node with
    | source =>
        change 0 < 1
        decide
    | target =>
        change ¬ True at notNormal
        exact False.elim (notNormal True.intro)

def demoRewrite : DemoNode → DemoNode → Prop
  | .source, .target => True
  | _, _ => False

noncomputable def demoConfluent :
    ConfluentAuthority (Node := DemoNode)
      (values := demoValues) (dynamics := demoDynamics)
      (inertia := demoInertia) (initial := demoInitial) where
  base := demoAuthority
  rewrite := demoRewrite
  selected sourceNode notNormal := by
    cases sourceNode with
    | source => trivial
    | target =>
        change ¬ True at notNormal
        exact False.elim (notNormal True.intro)
  decreases := by
    intro sourceNode targetNode edge
    cases sourceNode <;> cases targetNode <;> simp_all [demoRewrite, demoAuthority]
  localJoin := by
    intro sourceNode leftNode rightNode leftEdge rightEdge
    cases sourceNode <;> cases leftNode <;> cases rightNode <;>
      simp_all [demoRewrite]
    exact ⟨.target, .refl _, .refl _⟩
  normal_iff := by
    intro sourceNode
    cases sourceNode with
    | source =>
        constructor
        · intro impossible
          exact False.elim impossible
        · intro irreducible
          exact False.elim (irreducible .target trivial)
    | target =>
        constructor
        · intro _
          intro candidate edge
          cases candidate <;> simp_all [demoRewrite]
        · intro _
          trivial

noncomputable def demoResult : Result demoAuthority DemoNode.source where
  final := .target
  links := [demoLink]
  connected := ⟨demoLink_source, trivial⟩
  terminal_eq := by
    change RewriteChain.terminal demoDynamics demoInertia demoInitial demoSource
      [demoLink] = demoTarget
    simp [RewriteChain.terminal, demoLink_target]
  normal := trivial

theorem demo_normalizes :
    normalize demoAuthority DemoNode.source = some demoResult := by
  change normalizeFuel demoAuthority 1 DemoNode.source = some demoResult
  simp [normalizeFuel, demoAuthority, demoResult]

theorem demo_result_final : demoResult.final = DemoNode.target := rfl

theorem demo_result_link_count : demoResult.links.length = 1 := rfl

def demoExecutableFinal : DemoNode := .target

def demoExecutableLinkCount : Nat := 1

theorem demo_result_final_executable : demoResult.final = demoExecutableFinal := rfl

theorem demo_result_link_count_executable :
    demoResult.links.length = demoExecutableLinkCount := rfl

theorem demo_result_rules :
    (demoAuthority.package demoResult.final).trace.rules =
      [.oInsert, .oInsert, .lBegin] := by
  change demoTarget.trace.rules = _
  exact demoTarget_rules

theorem demo_result_actors :
    (demoAuthority.package demoResult.final).trace.actors =
      [.fiber 0, .fiber 1, .fiber 0] := by
  change demoTarget.trace.actors = _
  change (Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.witness.target
    demoDynamics demoInertia demoInitial).trace.actors = _
  rw [← Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.terminal_eq_target]
  exact Cordis.GlobalPaperTraceNormalization.Example.ActivationOrchestration.terminal_actors

theorem demo_normalizer_unique
    (left right : Result demoAuthority DemoNode.source)
    (leftEquality : normalize demoAuthority DemoNode.source = some left)
    (rightEquality : normalize demoAuthority DemoNode.source = some right) :
    demoAuthority.package left.final = demoAuthority.package right.final :=
  normalize_results_unique demoConfluent DemoNode.source left right leftEquality rightEquality

end Example

end Cordis.GlobalPaperTraceScopedConfluence
