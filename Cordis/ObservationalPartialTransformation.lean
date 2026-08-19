import Cordis.PartialTransformation
import Cordis.CoeffectQuotient
import Cordis.ContextualEquivalence
import Cordis.QuotientEffect

/-!
# Observational partial transformation monoids

This module extends the finite exact partial/Kleisli Definition 17/19/Theorem 42 analogue to
CORDIS Definition 33 contextual equivalence. A related pair of partial maps must agree on
definedness for related inputs and return related outputs when defined. This is stronger than
comparing successful outputs only and makes quotient-domain behavior explicit.

Exact partial independence does not by itself imply quotient independence: every generator must
also respect the contextual relation. `GeneratorRespects` names that additional Definition 36/37
obligation. The existing `CoeffectAt` respect fields and the quotient lift theorems prove it for
the current `Computation` semantics; no new operation law is assumed.

The main theorem is a finite, exact-context, partial/Kleisli observational analogue of paper
Theorem 42. It is not the paper's total quotient theorem: foreign transformations may be
undefined, yield stability is conditioned on successful foreign execution, and all closure words
are finite.
-/

set_option autoImplicit false

namespace Cordis.ObservationalPartialTransformation

open Cordis.MediatedIndependence
open Cordis.MediatedTheorem

universe u v w x

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
variable {coeffects : CoeffectFamily.{u, v, w} Key Value}

abbrev Equivalences (Key : Type u) (Value : Key → Type v) :=
  Coeffect.Observational.Equivalences Key Value
abbrev Context (Key : Type u) [DecidableEq Key] (Value : Key → Type v) :=
  Coeffect.Context Key Value

def contextRelation (coeffects : CoeffectFamily.{u, v, w} Key Value) :
    Context Key Value → Context Key Value → Prop :=
  Coeffect.Observational.Related (Coeffect.Observational.equivalencesOf coeffects)

/-!
## Related partial maps
-/

variable {State : Type x} {relation : State → State → Prop}

/-- Partial-map relatedness on related inputs. `OptionRelated` rules out a domain mismatch. -/
def MapsRelated
    (relation : State → State → Prop)
    (left right : Cordis.PartialTransformation.PartialMap State) : Prop :=
  ∀ {leftState rightState}, relation leftState rightState →
    Coeffect.Observational.OptionRelated relation (left leftState) (right rightState)

/-- A partial map descends to the quotient, including agreement of its partial domain. -/
def Respects
    (relation : State → State → Prop)
    (map : Cordis.PartialTransformation.PartialMap State) : Prop :=
  MapsRelated relation map map

/-- Related partial maps have the same success bit on related inputs. -/
theorem MapsRelated.isSome_eq
    {relation : State → State → Prop}
    {left right : Cordis.PartialTransformation.PartialMap State}
    (mapsRelated : MapsRelated relation left right)
    {leftState rightState : State} (statesRelated : relation leftState rightState) :
    (left leftState).isSome = (right rightState).isSome :=
  Coeffect.Observational.OptionRelated.isSome_eq (mapsRelated statesRelated)

/-- Bind related partial results through map families that preserve related values. -/
theorem optionRelated_bind
    {left right : Option State}
    {leftNext rightNext : State → Option State}
    (related : Coeffect.Observational.OptionRelated relation left right)
    (nextRelated : ∀ {leftValue rightValue}, relation leftValue rightValue →
      Coeffect.Observational.OptionRelated relation
        (leftNext leftValue) (rightNext rightValue)) :
    Coeffect.Observational.OptionRelated relation
      (left.bind leftNext) (right.bind rightNext) := by
  cases related with
  | none => exact Coeffect.Observational.OptionRelated.none
  | some valuesRelated => exact nextRelated valuesRelated

/-- Identity respects every relation on already-related inputs. -/
theorem respects_identity :
    Respects relation (Cordis.PartialTransformation.identity :
      Cordis.PartialTransformation.PartialMap State) := by
  intro left right related
  exact Coeffect.Observational.OptionRelated.some related

/-- Kleisli composition preserves quotient-respect. -/
theorem Respects.comp
    {relation : State → State → Prop}
    {outer inner : Cordis.PartialTransformation.PartialMap State}
    (outerRespects : Respects relation outer)
    (innerRespects : Respects relation inner) :
    Respects relation (Cordis.PartialTransformation.comp outer inner) := by
  intro left right related
  exact optionRelated_bind (innerRespects related) (fun valuesRelated ↦
    outerRespects valuesRelated)

/-- Related outer and inner maps compose directly in the Kleisli category. -/
theorem MapsRelated.comp
    {relation : State → State → Prop}
    {leftOuter rightOuter leftInner rightInner : Cordis.PartialTransformation.PartialMap State}
    (outerRelated : MapsRelated relation leftOuter rightOuter)
    (innerRelated : MapsRelated relation leftInner rightInner) :
    MapsRelated relation
      (Cordis.PartialTransformation.comp leftOuter leftInner)
      (Cordis.PartialTransformation.comp rightOuter rightInner) := by
  intro left right related
  exact optionRelated_bind (innerRelated related) (fun valuesRelated ↦
    outerRelated valuesRelated)

/-- Swap both maps and related inputs. -/
theorem MapsRelated.symm
    (symmetric : ∀ {left right : State}, relation left right → relation right left)
    {left right : Cordis.PartialTransformation.PartialMap State}
    (mapsRelated : MapsRelated relation left right) :
    MapsRelated relation right left := by
  intro rightState leftState related
  exact Coeffect.Observational.OptionRelated.symm symmetric (mapsRelated (symmetric related))

/-- Exact equality descends to observational map equality once the map respects the relation. -/
theorem mapsRelated_of_eq
    {relation : State → State → Prop}
    {left right : Cordis.PartialTransformation.PartialMap State}
    (leftRespects : Respects relation left) (equal : left = right) :
    MapsRelated relation left right := by
  subst right
  exact leftRespects

/-- Observational commutation on the quotient, with both composite domains explicit. -/
def Commutes
    (relation : State → State → Prop)
    (left right : Cordis.PartialTransformation.PartialMap State) : Prop :=
  MapsRelated relation
    (Cordis.PartialTransformation.comp left right)
    (Cordis.PartialTransformation.comp right left)

/-- Observational commutation is symmetric when the state relation is symmetric. -/
theorem Commutes.symm
    (symmetric : ∀ {left right : State}, relation left right → relation right left)
    {left right : Cordis.PartialTransformation.PartialMap State}
    (commutes : Commutes relation left right) : Commutes relation right left :=
  MapsRelated.symm symmetric commutes

/-!
## Relation-respecting generators and closures
-/

/-- One exact computation generator certified to respect contextual equivalence. -/
structure Generator
    (relation : Context Key Value → Context Key Value → Prop)
    (computation : OperationIndependence.Computation coeffects)
    (map : Cordis.PartialTransformation.PartialMap (Context Key Value)) : Prop where
  exact : Cordis.PartialTransformation.Generator computation map
  respects : Respects relation map

/-- The least relation-respecting Kleisli monoid of a computation. -/
abbrev Closure
    (relation : Context Key Value → Context Key Value → Prop)
    (computation : OperationIndependence.Computation coeffects) :
    Cordis.PartialTransformation.PartialMap (Context Key Value) → Prop :=
  Cordis.PartialTransformation.Closure (Generator relation computation)

/-- Every relation-respecting closure member is an exact computation-monoid member. -/
theorem Closure.toExact
    {relation : Context Key Value → Context Key Value → Prop}
    {computation : OperationIndependence.Computation coeffects}
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)}
    (member : Closure relation computation map) :
    Cordis.PartialTransformation.OfComputation computation map :=
  Cordis.PartialTransformation.Closure.mono (fun generated ↦ generated.exact) member

/-- Every relation-respecting closure member respects the quotient. -/
theorem Closure.respects
    {relation : Context Key Value → Context Key Value → Prop}
    {computation : OperationIndependence.Computation coeffects}
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)}
    (member : Closure relation computation map) : Respects relation map := by
  induction member with
  | identity => exact respects_identity
  | generator generated => exact generated.respects
  | comp _ _ outerHypothesis innerHypothesis =>
      exact outerHypothesis.comp innerHypothesis

/-- The explicit extra law needed to descend every exact computation generator to the quotient. -/
def GeneratorRespects
    (relation : Context Key Value → Context Key Value → Prop)
    (computation : OperationIndependence.Computation coeffects) : Prop :=
  ∀ {map}, Cordis.PartialTransformation.Generator computation map → Respects relation map

/-- Generator respect promotes every exact monoid member into the observational closure. -/
theorem Closure.ofExact
    {relation : Context Key Value → Context Key Value → Prop}
    {computation : OperationIndependence.Computation coeffects}
    (generatorsRespect : GeneratorRespects relation computation)
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)}
    (member : Cordis.PartialTransformation.OfComputation computation map) :
    Closure relation computation map := by
  induction member with
  | identity => exact .identity
  | generator generated => exact .generator ⟨generated, generatorsRespect generated⟩
  | comp _ _ outerHypothesis innerHypothesis =>
      exact .comp outerHypothesis innerHypothesis

/-- Under generator respect, the observational closure contains exactly the exact closure maps. -/
theorem closure_iff_exact
    {relation : Context Key Value → Context Key Value → Prop}
    {computation : OperationIndependence.Computation coeffects}
    (generatorsRespect : GeneratorRespects relation computation)
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)} :
    Closure relation computation map ↔
      Cordis.PartialTransformation.OfComputation computation map :=
  ⟨Closure.toExact, Closure.ofExact generatorsRespect⟩

/-!
## Relation-aware results and yield stability
-/

/-- Two total inverse functions represent the same quotient map on related inputs. -/
def FunctionsRelated
    (relation : State → State → Prop)
    (left right : State → State) : Prop :=
  ∀ {leftState rightState}, relation leftState rightState →
    relation (left leftState) (right rightState)

/-- Related proof-erased results retain related successors and related complete inverses. -/
structure RawResultRelated
    (relation : Context Key Value → Context Key Value → Prop)
    (left right : RawResult Key Value) : Prop where
  after : relation left.after right.after
  undo : FunctionsRelated relation left.undo right.undo

/-- Relation-aware partial yield stability. -/
def YieldStable
    (relation : Context Key Value → Context Key Value → Prop)
    (computation : OperationIndependence.Computation coeffects)
    (map : Cordis.PartialTransformation.PartialMap (Context Key Value)) : Prop :=
  ∀ seed result moved,
    evaluate computation seed = some result →
    map seed = some moved →
    ∃ movedResult,
      evaluate computation moved = some movedResult ∧
        FunctionsRelated relation movedResult.undo result.undo

/-- Observational partial/Kleisli analogue of Definition 19. -/
structure Independent
    (relation : Context Key Value → Context Key Value → Prop)
    (left right : OperationIndependence.Computation coeffects) : Prop where
  transformations_commute : ∀ {leftMap rightMap},
    Closure relation left leftMap → Closure relation right rightMap →
    Commutes relation leftMap rightMap
  left_yield_stable : ∀ {map}, Closure relation right map →
    YieldStable relation left map
  right_yield_stable : ∀ {map}, Closure relation left map →
    YieldStable relation right map

namespace Independent

/-- Observational independence is symmetric. -/
theorem symm
    {relation : Context Key Value → Context Key Value → Prop}
    (symmetric : ∀ {left right}, relation left right → relation right left)
    {left right : OperationIndependence.Computation coeffects}
    (independent : Independent relation left right) : Independent relation right left where
  transformations_commute := fun leftMember rightMember ↦
    Commutes.symm symmetric
      (independent.transformations_commute rightMember leftMember)
  left_yield_stable := independent.right_yield_stable
  right_yield_stable := independent.left_yield_stable

end Independent

/-!
## Exact-to-observational descent under explicit respect
-/

/-- Respect of a total Kleisli lift is exactly relation preservation by its underlying function. -/
theorem functionsRelated_of_total_respects
    {relation : Context Key Value → Context Key Value → Prop}
    {map : Context Key Value → Context Key Value}
    (respects : Respects relation (Cordis.PartialTransformation.total map)) :
    FunctionsRelated relation map map := by
  intro left right related
  have outputs := respects related
  change Coeffect.Observational.OptionRelated relation
    (some (map left)) (some (map right)) at outputs
  cases outputs with
  | some valuesRelated => exact valuesRelated

/-- Exact commutation descends to observational commutation when both maps respect the quotient. -/
theorem commutes_of_exact
    {relation : State → State → Prop}
    {left right : Cordis.PartialTransformation.PartialMap State}
    (exact : Cordis.PartialTransformation.Commutes left right)
    (leftRespects : Respects relation left) (rightRespects : Respects relation right) :
    Commutes relation left right := by
  intro leftState rightState statesRelated
  have reverseRespects : Respects relation (Cordis.PartialTransformation.comp right left) :=
    Respects.comp rightRespects leftRespects
  have outputsRelated := reverseRespects statesRelated
  rw [exact leftState]
  exact outputsRelated

/-- Exact yield stability becomes relation-aware once every yielded inverse generator respects
the quotient.
-/
theorem yieldStable_of_exact
    {relation : Context Key Value → Context Key Value → Prop}
    {computation : OperationIndependence.Computation coeffects}
    (generatorsRespect : GeneratorRespects relation computation)
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)}
    (exact : Cordis.PartialTransformation.YieldStable computation map) :
    YieldStable relation computation map := by
  intro seed result moved ran transformed
  obtain ⟨movedResult, movedRan, undoEqual⟩ := exact seed result moved ran transformed
  have inverseRespects : Respects relation
      (Cordis.PartialTransformation.total result.undo) :=
    generatorsRespect
      (Cordis.PartialTransformation.Generator.inverse seed result ran)
  have relatedUndo : FunctionsRelated relation result.undo result.undo :=
    functionsRelated_of_total_respects (relation := relation) (map := result.undo)
      inverseRespects
  refine ⟨movedResult, movedRan, ?_⟩
  rw [undoEqual]
  exact relatedUndo

/-- Exact partial transformation independence descends to the observational quotient precisely
when all generators of both computations respect that quotient.
-/
theorem independent_of_exact
    {relation : Context Key Value → Context Key Value → Prop}
    {left right : OperationIndependence.Computation coeffects}
    (leftGeneratorsRespect : GeneratorRespects relation left)
    (rightGeneratorsRespect : GeneratorRespects relation right)
    (exact : Cordis.PartialTransformation.Independent left right) :
    Independent relation left right where
  transformations_commute := by
    intro leftMap rightMap leftMember rightMember
    exact commutes_of_exact
      (exact.transformations_commute leftMember.toExact rightMember.toExact)
      leftMember.respects rightMember.respects
  left_yield_stable := by
    intro map member
    exact yieldStable_of_exact leftGeneratorsRespect
      (exact.left_yield_stable member.toExact)
  right_yield_stable := by
    intro map member
    exact yieldStable_of_exact rightGeneratorsRespect
      (exact.right_yield_stable member.toExact)

/-!
## Computations respect contextual equivalence
-/

/-- Paired local data from related seeds: successor and inverse respect the key relation, while
the heterogeneous outcome is exactly equal.
-/
structure ForwardDataRelated
    (key : Key) (op : (coeffects key).Op)
    (left right : OperationIndependence.ForwardData (coeffects key) op) : Prop where
  after : (coeffects key).equivalence.r left.after right.after
  undo : ∀ {leftCurrent rightCurrent},
    (coeffects key).equivalence.r leftCurrent rightCurrent →
      (coeffects key).equivalence.r (left.undo leftCurrent) (right.undo rightCurrent)
  outcome : left.outcome = right.outcome

/-- Related contexts agree on the domain of one operation and yield related complete local data. -/
theorem inspectForward_related
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    {left right : Context Key Value}
    (contextsRelated : contextRelation coeffects left right) :
    Coeffect.Observational.OptionRelated (ForwardDataRelated key op)
      (OperationIndependence.inspectForwardAt coeffects key op input left)
      (OperationIndependence.inspectForwardAt coeffects key op input right) := by
  have atKey := contextsRelated key
  cases leftLookup : left key with
  | none =>
      cases rightLookup : right key with
      | none =>
          simp [OperationIndependence.inspectForwardAt, leftLookup, rightLookup]
          exact Coeffect.Observational.OptionRelated.none
      | some rightValue =>
          rw [leftLookup, rightLookup] at atKey
          cases atKey
  | some leftValue =>
      cases rightLookup : right key with
      | none =>
          rw [leftLookup, rightLookup] at atKey
          cases atKey
      | some rightValue =>
          rw [leftLookup, rightLookup] at atKey
          cases atKey with
          | some valuesRelated =>
              letI := (coeffects key).enabledDecidable op input leftValue
              letI := (coeffects key).enabledDecidable op input rightValue
              by_cases leftEnabled : (coeffects key).Enabled op input leftValue
              · have rightEnabled : (coeffects key).Enabled op input rightValue :=
                  ((coeffects key).enabled_respects op input valuesRelated).mp leftEnabled
                simp [OperationIndependence.inspectForwardAt, leftLookup, rightLookup,
                  leftEnabled, rightEnabled]
                exact Coeffect.Observational.OptionRelated.some {
                  after := (coeffects key).after_respects op input valuesRelated
                    leftEnabled rightEnabled
                  undo := fun currentRelated ↦
                    (coeffects key).undo_respects op input valuesRelated leftEnabled
                      rightEnabled currentRelated
                  outcome := (coeffects key).outcome_respects op input valuesRelated
                    leftEnabled rightEnabled
                }
              · have rightDisabled : ¬(coeffects key).Enabled op input rightValue :=
                  fun enabled ↦ leftEnabled
                    (((coeffects key).enabled_respects op input valuesRelated).mpr enabled)
                simp [OperationIndependence.inspectForwardAt, leftLookup, rightLookup,
                  leftEnabled, rightDisabled]
                exact Coeffect.Observational.OptionRelated.none

/-- Related local data lifts to related whole-context successors and complete totalized inverses. -/
theorem rawStage_related
    (key : Key) {op : (coeffects key).Op}
    {leftBefore rightBefore : Context Key Value}
    {leftData rightData : OperationIndependence.ForwardData (coeffects key) op}
    (beforeRelated : contextRelation coeffects leftBefore rightBefore)
    (dataRelated : ForwardDataRelated key op leftData rightData) :
    RawResultRelated (contextRelation coeffects)
      (rawStage key leftBefore leftData) (rawStage key rightBefore rightData) := by
  constructor
  · exact Coeffect.Observational.setAt_related
      (Coeffect.Observational.equivalencesOf coeffects) beforeRelated key dataRelated.after
  · intro leftCurrent rightCurrent currentRelated
    cases leftLookup : leftCurrent key with
    | none =>
        cases rightLookup : rightCurrent key with
        | none => simpa [rawStage, liftDataUndo, leftLookup, rightLookup] using currentRelated
        | some rightValue =>
            have presence := Coeffect.Observational.related_isSome_eq
              (Coeffect.Observational.equivalencesOf coeffects) currentRelated key
            simp [leftLookup, rightLookup] at presence
    | some leftValue =>
        cases rightLookup : rightCurrent key with
        | none =>
            have presence := Coeffect.Observational.related_isSome_eq
              (Coeffect.Observational.equivalencesOf coeffects) currentRelated key
            simp [leftLookup, rightLookup] at presence
        | some rightValue =>
            have valuesRelated :=
              ((Coeffect.Observational.related_iff
                (Coeffect.Observational.equivalencesOf coeffects) leftCurrent rightCurrent).1
                currentRelated).2 key leftValue rightValue leftLookup rightLookup
            simp only [rawStage, liftDataUndo, leftLookup, rightLookup]
            change Coeffect.Observational.Related
              (Coeffect.Observational.equivalencesOf coeffects)
              (Coeffect.setAt leftCurrent key (leftData.undo leftValue))
              (Coeffect.setAt rightCurrent key (rightData.undo rightValue))
            exact Coeffect.Observational.setAt_related
              (Coeffect.Observational.equivalencesOf coeffects) currentRelated key
              (dataRelated.undo valuesRelated)

/-- Sequential composition preserves raw-result relatedness. -/
theorem RawResultRelated.comp
    {relation : Context Key Value → Context Key Value → Prop}
    {leftFirst rightFirst leftSecond rightSecond : RawResult Key Value}
    (firstRelated : RawResultRelated relation leftFirst rightFirst)
    (secondRelated : RawResultRelated relation leftSecond rightSecond) :
    RawResultRelated relation (leftFirst.comp leftSecond) (rightFirst.comp rightSecond) where
  after := secondRelated.after
  undo := fun currentsRelated ↦ firstRelated.undo (secondRelated.undo currentsRelated)

/-- Every finite outcome-mediated computation maps related inputs to results with exactly the same
partial domain, related successors, and related complete inverse functions.
-/
theorem evaluate_related
    (computation : OperationIndependence.Computation coeffects)
    {left right : Context Key Value}
    (contextsRelated : contextRelation coeffects left right) :
    Coeffect.Observational.OptionRelated
      (RawResultRelated (contextRelation coeffects))
      (evaluate computation left) (evaluate computation right) := by
  induction computation generalizing left right with
  | pure =>
      rw [evaluate_pure, evaluate_pure]
      exact Coeffect.Observational.OptionRelated.some {
        after := contextsRelated
        undo := fun related ↦ related
      }
  | step key op input next induction =>
      rw [evaluate_step, evaluate_step]
      have inspected := inspectForward_related key op input contextsRelated
      cases leftInspect : OperationIndependence.inspectForwardAt coeffects key op input left with
      | none =>
          cases rightInspect : OperationIndependence.inspectForwardAt coeffects key op input
            right with
          | none =>
              exact Coeffect.Observational.OptionRelated.none
          | some rightData =>
              rw [leftInspect, rightInspect] at inspected
              cases inspected
      | some leftData =>
          cases rightInspect : OperationIndependence.inspectForwardAt coeffects key op input
            right with
          | none =>
              rw [leftInspect, rightInspect] at inspected
              cases inspected
          | some rightData =>
              rw [leftInspect, rightInspect] at inspected
              cases inspected with
              | some dataRelated =>
                  change Coeffect.Observational.OptionRelated
                    (RawResultRelated (contextRelation coeffects))
                    (match evaluate (next leftData.outcome) (rawStage key left leftData).after with
                    | none => none
                    | some tail => some ((rawStage key left leftData).comp tail))
                    (match evaluate (next rightData.outcome)
                      (rawStage key right rightData).after with
                    | none => none
                    | some tail => some ((rawStage key right rightData).comp tail))
                  have outcomeEqual := dataRelated.outcome
                  rw [← outcomeEqual]
                  have stageRelated := rawStage_related key contextsRelated dataRelated
                  have tailRelated := induction leftData.outcome stageRelated.after
                  cases leftTail : evaluate (next leftData.outcome)
                    (rawStage key left leftData).after with
                  | none =>
                      cases rightTail : evaluate (next leftData.outcome)
                        (rawStage key right rightData).after with
                      | none =>
                          exact Coeffect.Observational.OptionRelated.none
                      | some rightResult =>
                          rw [leftTail, rightTail] at tailRelated
                          cases tailRelated
                  | some leftResult =>
                      cases rightTail : evaluate (next leftData.outcome)
                        (rawStage key right rightData).after with
                      | none =>
                          rw [leftTail, rightTail] at tailRelated
                          cases tailRelated
                      | some rightResult =>
                          rw [leftTail, rightTail] at tailRelated
                          cases tailRelated with
                          | some continuationRelated =>
                              exact Coeffect.Observational.OptionRelated.some
                                (stageRelated.comp continuationRelated)

/-- Related starting contexts give exactly the same computation definedness bit. -/
theorem evaluate_isSome_eq_of_related
    (computation : OperationIndependence.Computation coeffects)
    {left right : Context Key Value}
    (related : contextRelation coeffects left right) :
    (evaluate computation left).isSome = (evaluate computation right).isSome :=
  Coeffect.Observational.OptionRelated.isSome_eq (evaluate_related computation related)

/-!
## Every computation generator respects the quotient
-/

/-- Mapping related optional values through related result projections preserves domains and
related outputs.
-/
theorem optionRelated_map
    {First Second : Type x} {firstRelation : First → First → Prop}
    {secondRelation : Second → Second → Prop}
    {left right : Option First} {leftMap rightMap : First → Second}
    (related : Coeffect.Observational.OptionRelated firstRelation left right)
    (mapsRelated : ∀ {leftValue rightValue}, firstRelation leftValue rightValue →
      secondRelation (leftMap leftValue) (rightMap rightValue)) :
    Coeffect.Observational.OptionRelated secondRelation
      (left.map leftMap) (right.map rightMap) := by
  cases related with
  | none => exact Coeffect.Observational.OptionRelated.none
  | some valuesRelated =>
      exact Coeffect.Observational.OptionRelated.some (mapsRelated valuesRelated)

/-- The complete partial forward map of every computation respects contextual equivalence. -/
theorem forward_respects
    (computation : OperationIndependence.Computation coeffects) :
    Respects (contextRelation coeffects)
      (Cordis.PartialTransformation.forward computation) := by
  intro left right related
  unfold Cordis.PartialTransformation.forward
  exact optionRelated_map (evaluate_related computation related)
    (fun resultsRelated ↦ resultsRelated.after)

/-- Every complete inverse yielded by a computation respects contextual equivalence. -/
theorem yieldedInverse_respects
    (computation : OperationIndependence.Computation coeffects)
    (seed : Context Key Value) (result : RawResult Key Value)
    (ran : evaluate computation seed = some result) :
    Respects (contextRelation coeffects)
      (Cordis.PartialTransformation.total result.undo) := by
  have selfRelated := evaluate_related computation
    (Coeffect.Observational.related_refl
      (Coeffect.Observational.equivalencesOf coeffects) seed)
  rw [ran] at selfRelated
  have resultRelated : RawResultRelated (contextRelation coeffects) result result := by
    cases selfRelated with
    | some related => exact related
  intro left right related
  unfold Cordis.PartialTransformation.total
  exact Coeffect.Observational.OptionRelated.some (resultRelated.undo related)

/-- The current `CoeffectAt` quotient laws discharge the extra respect obligation for every
computation generator.
-/
theorem computation_generators_respect
    (computation : OperationIndependence.Computation coeffects) :
    GeneratorRespects (contextRelation coeffects) computation := by
  intro map generated
  cases generated with
  | forward => exact forward_respects computation
  | inverse seed result ran => exact yieldedInverse_respects computation seed result ran

/-- Therefore the observational closure contains every exact computation-monoid member. -/
theorem observationalClosure_of_exact
    (computation : OperationIndependence.Computation coeffects)
    {map : Cordis.PartialTransformation.PartialMap (Context Key Value)}
    (member : Cordis.PartialTransformation.OfComputation computation map) :
    Closure (contextRelation coeffects) computation map :=
  Closure.ofExact (computation_generators_respect computation) member

/-!
## Observational Definition 19 and Theorem 42 analogue
-/

/-- Finite exact-context partial/Kleisli observational analogue of Theorem 42. -/
theorem pairwiseOverlap_independent
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right) :
    Independent (contextRelation coeffects) left right :=
  independent_of_exact
    (computation_generators_respect left)
    (computation_generators_respect right)
    (Cordis.PartialTransformation.pairwiseOverlap_independent left right overlap)

/-- The earlier observational whole-run certificate is a separate weaker consequence. -/
theorem pairwiseOverlap_observationalWholeRun
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right) :
    BoundedPartialObservationalIndependence (coeffects := coeffects) left right :=
  (Cordis.PartialTransformation.pairwiseOverlap_independent left right overlap)
    |>.toBoundedPartial.toObservational

/-- Full observational closure and whole-run interchange are recorded without identifying them. -/
theorem pairwiseOverlap_full_and_wholeRun
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right) :
    Independent (contextRelation coeffects) left right ∧
      BoundedPartialObservationalIndependence (coeffects := coeffects) left right :=
  ⟨pairwiseOverlap_independent left right overlap,
    pairwiseOverlap_observationalWholeRun left right overlap⟩

/-!
## Respect is genuinely additional for arbitrary exact maps
-/

namespace RespectGap

structure Model where
  visible : Bool
  hidden : Bool
deriving DecidableEq, Repr

def modelRelation (left right : Model) : Prop := left.visible = right.visible

theorem relation_refl : ∀ state, modelRelation state state := fun _ ↦ rfl
theorem relation_symm : ∀ {left right}, modelRelation left right → modelRelation right left :=
  fun related ↦ related.symm
theorem relation_trans : ∀ {left middle right},
    modelRelation left middle → modelRelation middle right → modelRelation left right :=
  fun leftRelated rightRelated ↦ leftRelated.trans rightRelated

def bad (state : Model) : Model := ⟨state.hidden, state.hidden⟩

def badPartial : Cordis.PartialTransformation.PartialMap Model :=
  fun state ↦ some (bad state)

def left : Model := ⟨false, false⟩
def right : Model := ⟨false, true⟩

theorem inputs_related : modelRelation left right := rfl

/-- Exact identity/bad-map commutation holds. -/
theorem exact_commutes : Cordis.PartialTransformation.Commutes
    (Cordis.PartialTransformation.identity : Cordis.PartialTransformation.PartialMap Model)
    badPartial := by
  intro state
  simp

/-- The exact bad map does not descend to the observational quotient. -/
theorem bad_not_respects : ¬Respects modelRelation badPartial := by
  intro respects
  have outputs := respects inputs_related
  change Coeffect.Observational.OptionRelated modelRelation
    (some (bad left)) (some (bad right)) at outputs
  cases outputs with
  | some related => cases related

/-- Therefore exact commutation alone does not imply observational commutation. -/
theorem observational_commutation_fails :
    ¬Commutes modelRelation
      (Cordis.PartialTransformation.identity : Cordis.PartialTransformation.PartialMap Model)
      badPartial := by
  intro commutes
  have outputs := commutes inputs_related
  change Coeffect.Observational.OptionRelated modelRelation
    (some (bad left)) (some (bad right)) at outputs
  cases outputs with
  | some related => cases related

end RespectGap

/-!
## Heterogeneous branching instance
-/

namespace Example

open Cordis.MediatedTheorem.Example.IndependentBranching

/-- The existing `Nat → String` branch tree and independent `Bool` computation satisfy the full
observational closure theorem. Their local relations happen to be equality; nontrivial quotient
behavior is exercised by the generic respect theorems and `RespectGap` above.
-/
theorem independent : Independent (contextRelation demoCoeffects)
    leftComputation rightComputation :=
  pairwiseOverlap_independent leftComputation rightComputation overlap

end Example

end Cordis.ObservationalPartialTransformation
