import Cordis.TotalQuotientIndependence

/-!
# Domain-certified total quotient independence

`Cordis.TotalQuotientIndependence` makes a deliberately strong choice: a computation must
succeed on every finite context. Real mediated computations are partial because their typed
bindings may be absent. This module keeps that partiality while adding the weaker certificate
needed for a total/quotient reading on an explicitly named invariant domain.

The domain is not erased into an informal side condition. `DomainMap` stores totality and
domain preservation for its partial map, and `Closure` carries those witnesses through the
identity, forward, yielded-inverse, and composition constructors. `independent_of_partial`
then transports the existing finite observational Theorem-42 analogue to this certified
domain, without claiming unrestricted totality.
-/

set_option autoImplicit false

namespace Cordis.DomainTotalQuotientIndependence

open Cordis.MediatedIndependence
open Cordis.MediatedTheorem

universe u v w

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
variable {coeffects : CoeffectFamily.{u, v, w} Key Value}

abbrev Context (Key : Type u) [DecidableEq Key] (Value : Key → Type v) :=
  Coeffect.Context Key Value

abbrev Relation (coeffects : CoeffectFamily.{u, v, w} Key Value) :
    Context Key Value → Context Key Value → Prop :=
  Cordis.ObservationalPartialTransformation.contextRelation coeffects

abbrev PartialMap (Key : Type u) [DecidableEq Key] (Value : Key → Type v) :=
  Cordis.PartialTransformation.PartialMap (Context Key Value)

/-!
## Totality on an invariant domain
-/

structure DomainTotalComputation
    (coeffects : CoeffectFamily.{u, v, w} Key Value)
    (domain : Context Key Value → Prop) where
  computation : OperationIndependence.Computation coeffects
  total_on : ∀ context, domain context → ∃ result,
    evaluate computation context = some result ∧ domain result.after
  inverse_preserves : ∀ {seed : Context Key Value} {result : RawResult Key Value},
    evaluate computation seed = some result →
      ∀ current, domain current → domain (result.undo current)

noncomputable def resultAt
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain)
    (context : Context Key Value) (context_domain : domain context) :
    RawResult Key Value :=
  Classical.choose (program.total_on context context_domain)

theorem resultAt_spec
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain)
    (context : Context Key Value) (context_domain : domain context) :
    evaluate program.computation context = some (resultAt program context context_domain) :=
  (Classical.choose_spec (program.total_on context context_domain)).1

theorem resultAt_domain
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain)
    (context : Context Key Value) (context_domain : domain context) :
    domain (resultAt program context context_domain).after :=
  (Classical.choose_spec (program.total_on context context_domain)).2

/-!
## Domain maps and their generated closure
-/

structure DomainMap (domain : Context Key Value → Prop) where
  map : PartialMap Key Value
  total_on : ∀ context, domain context → ∃ after, map context = some after
  preserves : ∀ {context after}, domain context → map context = some after → domain after

def DomainMap.identity (domain : Context Key Value → Prop) : DomainMap domain where
  map := Cordis.PartialTransformation.identity
  total_on := by
    intro context _
    exact ⟨context, rfl⟩
  preserves := by
    intro context after context_domain equal
    have equal' : context = after := Option.some.inj equal
    cases equal'
    exact context_domain

noncomputable def DomainMap.forward
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain) : DomainMap domain where
  map := Cordis.PartialTransformation.forward program.computation
  total_on := by
    intro context context_domain
    refine ⟨(resultAt program context context_domain).after, ?_⟩
    simp [Cordis.PartialTransformation.forward, resultAt_spec program context context_domain]
  preserves := by
    intro context after context_domain equal
    simp [Cordis.PartialTransformation.forward,
      resultAt_spec program context context_domain] at equal
    rw [← equal]
    exact resultAt_domain program context context_domain

noncomputable def DomainMap.inverse
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain)
    (seed : Context Key Value) (seed_domain : domain seed) : DomainMap domain where
  map := Cordis.PartialTransformation.total
    (resultAt program seed seed_domain).undo
  total_on := by
    intro context _
    exact ⟨(resultAt program seed seed_domain).undo context, rfl⟩
  preserves := by
    intro context after context_domain equal
    simp [Cordis.PartialTransformation.total] at equal
    rw [← equal]
    exact program.inverse_preserves
      (resultAt_spec program seed seed_domain) context context_domain

def DomainMap.comp
    {domain : Context Key Value → Prop}
    (outer inner : DomainMap domain) : DomainMap domain where
  map := Cordis.PartialTransformation.comp outer.map inner.map
  total_on := by
    intro context context_domain
    obtain ⟨middle, middle_eq⟩ := inner.total_on context context_domain
    obtain ⟨after, after_eq⟩ := outer.total_on middle
      (inner.preserves context_domain middle_eq)
    refine ⟨after, ?_⟩
    simp [Cordis.PartialTransformation.comp, middle_eq, after_eq]
  preserves := by
    intro context after context_domain equal
    obtain ⟨middle, middle_eq⟩ := inner.total_on context context_domain
    have middle_domain := inner.preserves context_domain middle_eq
    have outer_equal : outer.map middle = some after := by
      simpa [Cordis.PartialTransformation.comp, middle_eq] using equal
    exact outer.preserves middle_domain outer_equal

inductive Closure
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain) :
    DomainMap domain → Prop where
  | identity : Closure program (DomainMap.identity domain)
  | forward : Closure program (DomainMap.forward program)
  | inverse (seed : Context Key Value) (seed_domain : domain seed) :
      Closure program (DomainMap.inverse program seed seed_domain)
  | comp {outer inner : DomainMap domain} :
      Closure program outer → Closure program inner →
      Closure program (DomainMap.comp outer inner)

theorem Closure.toExact
    {domain : Context Key Value → Prop}
    (program : DomainTotalComputation coeffects domain)
    {map : DomainMap domain} (member : Closure program map) :
    Cordis.PartialTransformation.OfComputation program.computation map.map := by
  induction member with
  | identity =>
      exact .identity
  | forward =>
      exact .generator .forward
  | inverse seed seed_domain =>
      exact .generator (.inverse seed (resultAt program seed seed_domain)
        (resultAt_spec program seed seed_domain))
  | comp outer_member inner_member ih_outer ih_inner =>
      exact .comp ih_outer ih_inner

/-!
## The certified quotient theorem
-/

structure DomainIndependent
    {domain : Context Key Value → Prop}
    (left right : DomainTotalComputation coeffects domain) : Prop where
  transformations_commute : ∀ {leftMap rightMap : DomainMap domain},
    Closure left leftMap → Closure right rightMap →
      ∀ before, domain before → ∃ leftAfter rightAfter,
        Cordis.PartialTransformation.comp leftMap.map rightMap.map before = some leftAfter ∧
        Cordis.PartialTransformation.comp rightMap.map leftMap.map before = some rightAfter ∧
        Relation coeffects leftAfter rightAfter
  left_yield_stable : ∀ {map : DomainMap domain}, Closure right map →
    ∀ {seed : Context Key Value} (_seed_domain : domain seed)
      {result : RawResult Key Value},
      evaluate left.computation seed = some result →
      ∃ moved movedResult,
        map.map seed = some moved ∧
        evaluate left.computation moved = some movedResult ∧
        Cordis.ObservationalPartialTransformation.FunctionsRelated
          (Relation coeffects) movedResult.undo result.undo
  right_yield_stable : ∀ {map : DomainMap domain}, Closure left map →
    ∀ {seed : Context Key Value} (_seed_domain : domain seed)
      {result : RawResult Key Value},
      evaluate right.computation seed = some result →
      ∃ moved movedResult,
        map.map seed = some moved ∧
        evaluate right.computation moved = some movedResult ∧
        Cordis.ObservationalPartialTransformation.FunctionsRelated
          (Relation coeffects) movedResult.undo result.undo

theorem independent_of_partial
    {domain : Context Key Value → Prop}
    (left right : DomainTotalComputation coeffects domain)
    (certificate : Cordis.ObservationalPartialTransformation.Independent
      (Relation coeffects) left.computation right.computation) :
    DomainIndependent left right where
  transformations_commute := by
    intro leftMap rightMap left_member right_member before before_domain
    obtain ⟨middle, middle_eq⟩ := rightMap.total_on before before_domain
    have middle_domain := rightMap.preserves before_domain middle_eq
    obtain ⟨left_after, left_eq⟩ := leftMap.total_on middle middle_domain
    obtain ⟨right_middle, right_eq⟩ := leftMap.total_on before before_domain
    have right_middle_domain := leftMap.preserves before_domain right_eq
    obtain ⟨right_after, right_after_eq⟩ := rightMap.total_on right_middle right_middle_domain
    have related := certificate.transformations_commute
      (Cordis.ObservationalPartialTransformation.observationalClosure_of_exact
        left.computation (Closure.toExact left left_member))
      (Cordis.ObservationalPartialTransformation.observationalClosure_of_exact
        right.computation (Closure.toExact right right_member))
      (leftState := before) (rightState := before)
      (Coeffect.Observational.related_refl
        (Coeffect.Observational.equivalencesOf coeffects) before)
    have left_comp_eq :
        Cordis.PartialTransformation.comp leftMap.map rightMap.map before =
          some left_after := by
      simpa [Cordis.PartialTransformation.comp, middle_eq] using left_eq
    have right_comp_eq :
        Cordis.PartialTransformation.comp rightMap.map leftMap.map before =
          some right_after := by
      simpa [Cordis.PartialTransformation.comp, right_eq] using right_after_eq
    refine ⟨left_after, right_after, left_comp_eq, right_comp_eq, ?_⟩
    · change Coeffect.Observational.OptionRelated (Relation coeffects)
        (Cordis.PartialTransformation.comp leftMap.map rightMap.map before)
        (Cordis.PartialTransformation.comp rightMap.map leftMap.map before) at related
      rw [left_comp_eq, right_comp_eq] at related
      cases related with
      | some related => exact related
  left_yield_stable := by
    intro map map_member seed seed_domain result ran
    obtain ⟨moved, moved_eq⟩ := map.total_on seed seed_domain
    obtain ⟨moved_result, moved_ran, inverse_related⟩ :=
      certificate.left_yield_stable
        (Cordis.ObservationalPartialTransformation.observationalClosure_of_exact
          right.computation (Closure.toExact right map_member))
        seed result moved ran moved_eq
    exact ⟨moved, moved_result, moved_eq, moved_ran, inverse_related⟩
  right_yield_stable := by
    intro map map_member seed seed_domain result ran
    obtain ⟨moved, moved_eq⟩ := map.total_on seed seed_domain
    obtain ⟨moved_result, moved_ran, inverse_related⟩ :=
      certificate.right_yield_stable
        (Cordis.ObservationalPartialTransformation.observationalClosure_of_exact
          left.computation (Closure.toExact left map_member))
        seed result moved ran moved_eq
    exact ⟨moved, moved_result, moved_eq, moved_ran, inverse_related⟩

theorem pairwiseOverlap_independent
    {domain : Context Key Value → Prop}
    (left right : DomainTotalComputation coeffects domain)
    (overlap : PairwiseOverlap coeffects left.computation right.computation) :
    DomainIndependent left right :=
  independent_of_partial left right
    (Cordis.ObservationalPartialTransformation.pairwiseOverlap_independent
      left.computation right.computation overlap)

/-!
## A nontrivial typed fixture
-/

namespace Example

open Cordis.Coeffect.Quotient.Example

def presentDomain (context : Context ExampleKey ExampleValue) : Prop :=
  ∃ counter label, context .counter = some counter ∧ context .label = some label

def counterComputation :
    OperationIndependence.Computation Cordis.Coeffect.Quotient.Example.coeffects :=
  .step .counter counterOp counterAmount (fun _ ↦ .pure)

def labelInput : labelCoeffect.Input (show labelCoeffect.Op from ()) :=
  show String from "-next"

def labelComputation :
    OperationIndependence.Computation Cordis.Coeffect.Quotient.Example.coeffects :=
  .step .label (show labelCoeffect.Op from ()) labelInput (fun _ ↦ .pure)

theorem counter_total_on
    {context : Context ExampleKey ExampleValue}
    (counter : Nat) (label : String)
    (counter_eq : context .counter = some counter)
    (label_eq : context .label = some label) :
    ∃ result, evaluate counterComputation context = some result ∧
      presentDomain result.after := by
  unfold counterComputation
  have eval_step := @Cordis.MediatedTheorem.evaluate_step
    Cordis.Coeffect.Quotient.Example.ExampleKey inferInstance
    Cordis.Coeffect.Quotient.Example.ExampleValue
    Cordis.Coeffect.Quotient.Example.coeffects
    .counter counterOp counterAmount (fun _ ↦ .pure) context
  rw [eval_step]
  simp [OperationIndependence.inspectForwardAt, counter_eq,
    Cordis.Coeffect.Quotient.Example.coeffects,
    Cordis.Coeffect.Quotient.Example.counterCoeffect,
    Cordis.MediatedTheorem.rawStage, Cordis.MediatedTheorem.RawResult.comp,
    presentDomain]
  exact ⟨⟨counter + 4, by
      change some (counter + 4) = some (counter + 4)
      rfl⟩, ⟨label, label_eq⟩⟩

theorem label_total_on
    {context : Context ExampleKey ExampleValue}
    (counter : Nat) (label : String)
    (counter_eq : context .counter = some counter)
    (label_eq : context .label = some label) :
    ∃ result, evaluate labelComputation context = some result ∧ presentDomain result.after := by
  unfold labelComputation
  have eval_step := @Cordis.MediatedTheorem.evaluate_step
    Cordis.Coeffect.Quotient.Example.ExampleKey inferInstance
    Cordis.Coeffect.Quotient.Example.ExampleValue
    Cordis.Coeffect.Quotient.Example.coeffects
    .label (show labelCoeffect.Op from ()) labelInput (fun _ ↦ .pure) context
  rw [eval_step]
  simp [OperationIndependence.inspectForwardAt, label_eq,
    Cordis.Coeffect.Quotient.Example.coeffects,
    Cordis.Coeffect.Quotient.Example.labelCoeffect,
    Cordis.MediatedTheorem.rawStage, Cordis.MediatedTheorem.RawResult.comp,
    presentDomain]
  exact ⟨⟨counter, counter_eq⟩, ⟨label ++ "-next", by
      change some (label ++ "-next") = some (label ++ "-next")
      rfl⟩⟩

theorem counter_inverse_preserves
    {seed : Context ExampleKey ExampleValue} {result : RawResult ExampleKey ExampleValue}
    (ran : evaluate counterComputation seed = some result)
    {current : Context ExampleKey ExampleValue} (counter : Nat) (label : String)
    (counter_eq : current .counter = some counter)
    (label_eq : current .label = some label) :
    presentDomain (result.undo current) := by
  unfold evaluate at ran
  simp [counterComputation] at ran
  obtain ⟨applied, run_eq, result_eq⟩ := ran
  subst result
  rw [OperationIndependence.Computation.run.eq_def] at run_eq
  dsimp at run_eq
  split at run_eq
  · contradiction
  · rename_i value lookup
    split at run_eq
    · rename_i enabled
      cases run_eq
      simp [presentDomain, Cordis.Effect.identity, Coeffect.CoeffectAt.lift,
        Cordis.MediatedTheorem.RawResult.ofApplied,
        Cordis.Coeffect.Quotient.Example.coeffects,
        Cordis.Coeffect.Quotient.Example.counterCoeffect] at *
      rw [counter_eq]
      exact ⟨⟨counter - 4, by
          change some (counter - 4) = some (counter - 4)
          rfl⟩, ⟨label, label_eq⟩⟩
    · contradiction

theorem label_inverse_preserves
    {seed : Context ExampleKey ExampleValue} {result : RawResult ExampleKey ExampleValue}
    (ran : evaluate labelComputation seed = some result)
    {current : Context ExampleKey ExampleValue} (counter : Nat) (label : String)
    (counter_eq : current .counter = some counter)
    (label_eq : current .label = some label) :
    presentDomain (result.undo current) := by
  unfold evaluate at ran
  simp [labelComputation] at ran
  obtain ⟨applied, run_eq, result_eq⟩ := ran
  subst result
  rw [OperationIndependence.Computation.run.eq_def] at run_eq
  dsimp at run_eq
  split at run_eq
  · contradiction
  · rename_i value lookup
    split at run_eq
    · rename_i enabled
      cases run_eq
      simp [presentDomain, Cordis.Effect.identity, Coeffect.CoeffectAt.lift,
        Cordis.MediatedTheorem.RawResult.ofApplied,
        Cordis.Coeffect.Quotient.Example.coeffects,
        Cordis.Coeffect.Quotient.Example.labelCoeffect] at *
      rw [label_eq]
      exact ⟨⟨counter, counter_eq⟩, ⟨value, by rfl⟩⟩
    · contradiction

def counterTotal : DomainTotalComputation
    Cordis.Coeffect.Quotient.Example.coeffects presentDomain where
  computation := counterComputation
  total_on := by
    intro context domain
    rcases domain with ⟨counter, label, counter_eq, label_eq⟩
    exact counter_total_on counter label counter_eq label_eq
  inverse_preserves := by
    intro seed result ran current current_domain
    rcases current_domain with ⟨counter, label, counter_eq, label_eq⟩
    exact counter_inverse_preserves ran counter label counter_eq label_eq

def labelTotal : DomainTotalComputation
    Cordis.Coeffect.Quotient.Example.coeffects presentDomain where
  computation := labelComputation
  total_on := by
    intro context domain
    rcases domain with ⟨counter, label, counter_eq, label_eq⟩
    exact label_total_on counter label counter_eq label_eq
  inverse_preserves := by
    intro seed result ran current current_domain
    rcases current_domain with ⟨counter, label, counter_eq, label_eq⟩
    exact label_inverse_preserves ran counter label counter_eq label_eq

theorem overlap : PairwiseOverlap
    Cordis.Coeffect.Quotient.Example.coeffects counterComputation labelComputation := by
  intro leftStage rightStage leftOccurs rightOccurs
  cases leftOccurs with
  | root =>
      cases rightOccurs with
      | root =>
          exact OperationIndependence.distinctKeys_finiteIndependent
            Cordis.Coeffect.Quotient.Example.coeffects .counter .label
            (by intro equal; cases equal)
      | continuation _ impossible => cases impossible
  | continuation _ impossible => cases impossible

theorem domainIndependent : DomainIndependent counterTotal labelTotal :=
  pairwiseOverlap_independent counterTotal labelTotal overlap

def initial : Context ExampleKey ExampleValue :=
  Coeffect.setAt
    (Coeffect.setAt (Coeffect.empty : Context ExampleKey ExampleValue)
      .counter (show ExampleValue .counter from (3 : Nat)))
    .label (show ExampleValue .label from ("a" : String))

theorem initial_domain : presentDomain initial := by
  exact ⟨show ExampleValue .counter from (3 : Nat),
    show ExampleValue .label from ("a" : String),
    by simp [initial, Coeffect.setAt], by simp [initial, Coeffect.setAt]⟩

theorem counter_is_partial :
    evaluate counterComputation (empty : Context ExampleKey ExampleValue) = none := rfl

theorem executable_commute : ∃ leftAfter rightAfter,
    Cordis.PartialTransformation.comp
      (DomainMap.forward counterTotal).map (DomainMap.forward labelTotal).map initial =
        some leftAfter ∧
      Cordis.PartialTransformation.comp
        (DomainMap.forward labelTotal).map (DomainMap.forward counterTotal).map initial =
        some rightAfter ∧
      Relation Cordis.Coeffect.Quotient.Example.coeffects leftAfter rightAfter :=
  domainIndependent.transformations_commute .forward .forward initial initial_domain

end Example

end Cordis.DomainTotalQuotientIndependence
