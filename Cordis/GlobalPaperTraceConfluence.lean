import Cordis.GlobalPaperTraceNormalizer

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceConfluence

universe u

variable {Node : Type u}

/-! ## A finite decreasing rewrite kernel -/

inductive Path (step : Node → Node → Prop) : Node → Node → Prop where
  | refl (node : Node) : Path step node node
  | cons {source middle target : Node} :
      step source middle → Path step middle target → Path step source target

namespace Path

theorem trans {step : Node → Node → Prop} {source middle target : Node} :
    Path step source middle → Path step middle target → Path step source target
  | .refl _, right => right
  | .cons edge tail, right => .cons edge (trans tail right)

end Path

def Joinable (step : Node → Node → Prop) (left right : Node) : Prop :=
  ∃ target, Path step left target ∧ Path step right target

structure DecreasingSystem (Node : Type u) where
  step : Node → Node → Prop
  measure : Node → Nat
  decreases : ∀ {source target}, step source target → measure target < measure source
  localJoin : ∀ {source left right},
    step source left → step source right → Joinable step left right

theorem measure_le_of_path
    (system : DecreasingSystem Node)
    {source target : Node} :
    Path system.step source target → system.measure target ≤ system.measure source := by
  intro path
  induction path with
  | refl => exact Nat.le_refl _
  | cons edge tail ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (system.decreases edge))

theorem global_join
    (system : DecreasingSystem Node)
    {source left right : Node}
    (leftPath : Path system.step source left)
    (rightPath : Path system.step source right) :
    Joinable system.step left right := by
  have aux : ∀ fuel : Nat, ∀ node : Node, system.measure node = fuel →
      ∀ {left right : Node},
        Path system.step node left → Path system.step node right →
          Joinable system.step left right := by
    intro fuel
    apply WellFounded.induction Nat.lt_wfRel.wf fuel
    intro fuel ih node nodeMeasure left right leftPath rightPath
    cases leftPath with
    | refl =>
        exact ⟨right, rightPath, .refl right⟩
    | @cons _ leftMiddle _ leftEdge leftTail =>
        cases rightPath with
        | refl =>
            exact ⟨left, .refl left, .cons leftEdge leftTail⟩
        | @cons _ rightMiddle _ rightEdge rightTail =>
            obtain ⟨join, leftToJoin, rightToJoin⟩ :=
              system.localJoin leftEdge rightEdge
            have leftMeasure : system.measure leftMiddle < fuel := by
              simpa [nodeMeasure] using system.decreases leftEdge
            have rightMeasure : system.measure rightMiddle < fuel := by
              simpa [nodeMeasure] using system.decreases rightEdge
            obtain ⟨leftCommon, leftEndPath, leftJoinPath⟩ :=
              ih (system.measure leftMiddle) leftMeasure leftMiddle rfl leftTail leftToJoin
            obtain ⟨rightCommon, rightEndPath, rightJoinPath⟩ :=
              ih (system.measure rightMiddle) rightMeasure rightMiddle rfl rightTail rightToJoin
            have joinMeasure : system.measure join < fuel := by
              exact Nat.lt_of_le_of_lt (measure_le_of_path system leftToJoin)
                (by simpa [nodeMeasure] using system.decreases leftEdge)
            obtain ⟨common, leftCommonPath, rightCommonPath⟩ :=
              ih _ joinMeasure _ rfl leftJoinPath rightJoinPath
            exact ⟨common, leftEndPath.trans leftCommonPath,
              rightEndPath.trans rightCommonPath⟩
  exact aux (system.measure source) source rfl leftPath rightPath

def Irreducible (step : Node → Node → Prop) (node : Node) : Prop :=
  ∀ target, ¬ step node target

theorem path_eq_of_irreducible
    {step : Node → Node → Prop}
    {source target : Node}
    (irreducible : Irreducible step source)
    (path : Path step source target) :
    target = source := by
  cases path with
  | refl => rfl
  | cons edge _ => exact False.elim (irreducible _ edge)

structure NormalForm (system : DecreasingSystem Node) (source : Node) where
  endpoint : Node
  path : Path system.step source endpoint
  irreducible : Irreducible system.step endpoint

theorem NormalForm.endpoint_eq
    (system : DecreasingSystem Node)
    {source : Node}
    (left right : NormalForm system source) :
    left.endpoint = right.endpoint := by
  obtain ⟨join, leftPath, rightPath⟩ := global_join system left.path right.path
  exact (path_eq_of_irreducible left.irreducible leftPath).symm.trans
    (path_eq_of_irreducible right.irreducible rightPath)

/-! ## A nontrivial finite branching witness -/

inductive BoolStep : (Bool × Bool) → (Bool × Bool) → Prop where
  | left (right : Bool) : BoolStep (true, right) (false, right)
  | right (left : Bool) : BoolStep (left, true) (left, false)

def boolMeasure (state : Bool × Bool) : Nat :=
  (if state.1 then 1 else 0) + (if state.2 then 1 else 0)

theorem bool_decreases {source target : Bool × Bool} (step : BoolStep source target) :
    boolMeasure target < boolMeasure source := by
  cases step <;> simp [boolMeasure]

theorem bool_localJoin {source left right : Bool × Bool}
    (leftStep : BoolStep source left) (rightStep : BoolStep source right) :
    Joinable BoolStep left right := by
  cases leftStep with
  | left rightValue =>
      cases rightStep with
      | left => exact ⟨_, .refl _, .refl _⟩
      | right =>
          exact ⟨(false, false), .cons (.right false) (.refl _),
            .cons (.left false) (.refl _)⟩
  | right leftValue =>
      cases rightStep with
      | left =>
          exact ⟨(false, false), .cons (.left false) (.refl _),
            .cons (.right false) (.refl _)⟩
      | right => exact ⟨_, .refl _, .refl _⟩

def boolSystem : DecreasingSystem (Bool × Bool) where
  step := BoolStep
  measure := boolMeasure
  decreases := bool_decreases
  localJoin := bool_localJoin

def boolStart : Bool × Bool := (true, true)

theorem boolLeftPath : Path BoolStep boolStart (false, false) :=
  .cons (.left true) (.cons (.right false) (.refl _))

theorem boolRightPath : Path BoolStep boolStart (false, false) :=
  .cons (.right true) (.cons (.left false) (.refl _))

theorem bool_normal : Irreducible BoolStep (false, false) := by
  intro target step
  cases step

def boolLeftNormal : NormalForm boolSystem boolStart where
  endpoint := (false, false)
  path := boolLeftPath
  irreducible := bool_normal

def boolRightNormal : NormalForm boolSystem boolStart where
  endpoint := (false, false)
  path := boolRightPath
  irreducible := bool_normal

theorem bool_normal_forms_unique :
    boolLeftNormal.endpoint = boolRightNormal.endpoint :=
  NormalForm.endpoint_eq boolSystem boolLeftNormal boolRightNormal

/-! ## The confluence kernel applied to the CORDIS trace normalizer

The normalizer's result type retains a connected list of rewrite links, but the
selected-link fact is not implicit in that list.  `AuthorityLinked` makes the
selection proof explicit.  A `ConfluentAuthority` then adds only the local
joinability law needed by `global_join`; no CORDIS dynamics are silently
treated as confluent.
-/

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation Cordis.GlobalPaperTraceNormalization
open Cordis.GlobalPaperTraceNormalizer

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

def AuthorityStep
    (authority : Authority values dynamics inertia initial)
    (source target : Package values dynamics inertia initial) : Prop :=
  ∃ notNormal : ¬ authority.normal source,
    (authority.step source notNormal).val.target dynamics inertia initial = target

def AuthorityLinked
    (authority : Authority values dynamics inertia initial)
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
  base : Authority values dynamics inertia initial
  localJoin : ∀ {source left right : Package values dynamics inertia initial},
    AuthorityStep base source left →
      AuthorityStep base source right →
        Joinable (AuthorityStep base) left right

def authoritySystem
    (authority : ConfluentAuthority values dynamics inertia initial) :
    DecreasingSystem (Package values dynamics inertia initial) where
  step := AuthorityStep authority.base
  measure := authority.base.measure
  decreases := by
    intro source target edge
    obtain ⟨notNormal, targetEq⟩ := edge
    rw [← targetEq]
    exact authority.base.decreases source notNormal
  localJoin := authority.localJoin

theorem path_of_authorityLinked
    (authority : Authority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) :
    ∀ (links : List (Link values dynamics inertia initial)),
      AuthorityLinked authority source links →
        Path (AuthorityStep authority) source
          (RewriteChain.terminal dynamics inertia initial source links)
  | [], _ => .refl source
  | link :: rest, evidence => by
      obtain ⟨notNormal, linkEq, tail⟩ := evidence
      subst link
      exact .cons ⟨notNormal, rfl⟩
        (path_of_authorityLinked authority
          ((authority.step source notNormal).val.target dynamics inertia initial)
          rest tail)

theorem normalizeFuel_authorityLinked
    (authority : Authority values dynamics inertia initial) :
    ∀ (fuel : Nat) (source : Package values dynamics inertia initial)
      (result : Result authority source),
      normalizeFuel authority fuel source = some result →
        AuthorityLinked authority source result.links
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
          exact normalizeFuel_authorityLinked authority fuel
            chosen.val.target tail tailEquality

theorem normalize_authorityLinked
    (authority : Authority values dynamics inertia initial)
    (source : Package values dynamics inertia initial) (result : Result authority source)
    (equality : normalize authority source = some result) :
    AuthorityLinked authority source result.links := by
  exact normalizeFuel_authorityLinked authority (authority.measure source) source result
    (by simpa [normalize] using equality)

theorem normal_irreducible
    (authority : Authority values dynamics inertia initial)
    {source : Package values dynamics inertia initial} (normal : authority.normal source) :
    Irreducible (AuthorityStep authority) source := by
  intro target edge
  exact edge.choose normal

theorem normalize_results_unique
    (authority : ConfluentAuthority values dynamics inertia initial)
    (source : Package values dynamics inertia initial)
    (left right : Result authority.base source)
    (leftEquality : normalize authority.base source = some left)
    (rightEquality : normalize authority.base source = some right) :
    left.final = right.final := by
  have leftEvidence := normalize_authorityLinked authority.base source left leftEquality
  have rightEvidence := normalize_authorityLinked authority.base source right rightEquality
  have leftPath :
      Path (AuthorityStep authority.base) source left.final := by
    rw [← left.terminal_eq]
    exact path_of_authorityLinked authority.base source left.links leftEvidence
  have rightPath :
      Path (AuthorityStep authority.base) source right.final := by
    rw [← right.terminal_eq]
    exact path_of_authorityLinked authority.base source right.links rightEvidence
  exact NormalForm.endpoint_eq (authoritySystem authority)
    { endpoint := left.final
      path := leftPath
      irreducible := normal_irreducible authority.base left.normal }
    { endpoint := right.final
      path := rightPath
      irreducible := normal_irreducible authority.base right.normal }

namespace Example

open Cordis.GlobalPaperTraceNormalizer.Example

abbrev exampleValues := Cordis.GlobalPaperTraceNormalizer.Example.exampleValues
abbrev exampleDynamics := Cordis.GlobalPaperTraceNormalizer.Example.exampleDynamics
abbrev exampleInertia := Cordis.GlobalPaperTraceNormalizer.Example.exampleInertia
abbrev exampleInitial := Cordis.GlobalPaperTraceNormalizer.Example.exampleInitial
abbrev examplePackage := Cordis.GlobalPaperTraceNormalizer.Example.emptySource

def emptyConfluent :
    ConfluentAuthority exampleValues exampleDynamics exampleInertia exampleInitial where
  base := emptyAuthority
  localJoin := by
    intro source left right leftStep _
    exact False.elim (leftStep.choose (by trivial))

theorem empty_normalizer_unique
    (left right : Result emptyConfluent.base examplePackage)
    (leftEquality : normalize emptyConfluent.base examplePackage = some left)
    (rightEquality : normalize emptyConfluent.base examplePackage = some right) :
    left.final = right.final :=
  normalize_results_unique emptyConfluent examplePackage left right leftEquality rightEquality

end Example

end Cordis.GlobalPaperTraceConfluence
