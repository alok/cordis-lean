import Cordis.Codec
import Cordis.GenericHarness
import Cordis.Tool
import Cordis.ToolWire

/-!
# Dependent-choice generic harness example

One Boolean request selects either a `Nat` or `String` response type. Both requests pass the
tool admission boundary, but the exact-call policy permits the numeric request and rejects the
text request before provider dispatch.
-/

namespace Cordis.Examples.DependentChoice

open Cordis

/-- A structured model demonstrating that the generic runner is not specialized to counters. -/
structure Workspace where
  revision : Nat
  label : String
deriving BEq, DecidableEq, Repr

inductive Capability where
  | inspect
deriving BEq, DecidableEq, Repr

inductive Operation where
  | choose
deriving BEq, DecidableEq, Repr

/-- The request value chooses its result type without erasing either branch into a sum. -/
def SelectedOutput : Bool -> Type
  | false => String
  | true => Nat

def choiceSpec : ToolSpec Workspace Capability where
  name := "workspace_choose"
  description := "Choose the workspace revision or label with a dependent result type"
  Input := Bool
  Output := SelectedOutput
  Failure _ := String
  pre _ _ := True
  post input before result after :=
    match input with
    | false =>
        match result with
        | .ok value => value = before.label ∧ after = before
        | .error _ => after = before
    | true =>
        match result with
        | .ok value => value = before.revision ∧ after = before
        | .error _ => after = before
  required _ capability := capability = .inspect
  emission := .pure

/-- The request Boolean definitionally selects the exact output type. -/
theorem request_selects_exact_output_type :
    choiceSpec.Output true = Nat ∧ choiceSpec.Output false = String :=
  ⟨rfl, rfl⟩

/-- A provider whose two branches prove their branch-specific result and model postconditions. -/
def choiceTool : ToolSpec.VerifiedTool choiceSpec where
  execute
    | ⟨false, before, _granted, _precondition, _authorized⟩ => {
        result := .ok before.label
        after := before
        postcondition := ⟨rfl, rfl⟩
      }
    | ⟨true, before, _granted, _precondition, _authorized⟩ => {
        result := .ok before.revision
        after := before
        postcondition := ⟨rfl, rfl⟩
      }

def catalog : ToolCatalog Workspace Capability where
  Tool := Operation
  toolDecEq := inferInstance
  spec
    | .choose => choiceSpec

def implementation : (tool : catalog.Tool) -> ToolSpec.VerifiedTool (catalog.spec tool)
  | .choose => choiceTool

def providerId : ProviderId := {
  domain := "example.dependent-choice"
  name := "choose"
  major := 1
}

def provider (tool : Operation) : Provider catalog.signature tool :=
  catalog.provider tool providerId (implementation tool)

def needs : Needs catalog.signature := fun _ => True

def needsDecidable (tool : Operation) : Decidable (needs tool) :=
  isTrue trivial

def registry : Registry catalog.signature
  | .choose => some (provider .choose)

def view : View catalog.signature registry needs where
  resolve operation _ := by
    cases operation
    exact { provider := provider .choose, present := rfl }

private def resolveTool : String -> Option Operation
  | "workspace_choose" => some .choose
  | _ => none

private def certifyChoiceAdmission
    (input : Bool)
    (before : Workspace)
    (granted : Capability -> Prop)
    (grantedDecidable : (capability : Capability) -> Decidable (granted capability)) :
    Except String (AdmissionEvidence choiceSpec input before granted) :=
  match grantedDecidable .inspect with
  | .isTrue hasInspect =>
      .ok {
        precondition := trivial
        authorized := by
          intro capability required
          change capability = Capability.inspect at required
          subst capability
          exact hasInspect
      }
  | .isFalse _ => .error "workspace_choose requires inspect capability"

def wire : ToolWire catalog where
  resolve := resolveTool
  resolve_name tool := by cases tool <;> rfl
  inputCodec
    | .choose => Codec.bool
  outputCodec
    | .choose, false => Codec.string
    | .choose, true => Codec.nat
  failureCodec
    | .choose, _ => Codec.string
  certifyAdmission
    | .choose, input, before, granted, decideGranted =>
        certifyChoiceAdmission input before granted decideGranted

def granted
    (_model : Workspace)
    (_raw : RawCall)
    (capability : Capability) : Prop :=
  capability = .inspect

def grantedDecidable
    (model : Workspace)
    (raw : RawCall)
    (capability : Capability) : Decidable (granted model raw capability) :=
  by
    cases capability
    exact isTrue rfl

abbrev Call := AuthorizedCall catalog.signature needs

/-- The proof family retained when policy rejects the exact label-selecting call. -/
def SelectsLabel (call : Call) : Prop :=
  match call.op with
  | .choose => call.request.input = false

structure PolicyRejected (call : Call) : Type where
  selectsLabel : SelectsLabel call

def renderPolicyRejected (_call : Call) (_reason : PolicyRejected _call) : String :=
  "label output rejected by exact-call policy"

/-- Revision calls are allowed; label calls retain an indexed denial certificate. -/
def decide
    (_before : Workspace)
    (_raw : RawCall)
    (call : Call) : GenericHarness.PolicyDecision PolicyRejected call := by
  cases input_eq : call.request.input with
  | false =>
      exact .reject .deny (by decide) {
        selectsLabel := by
          unfold SelectsLabel
          cases call.op
          exact input_eq
      }
  | true => exact .allow

def config : GenericHarness.Config Workspace Capability where
  catalog := catalog
  wire := wire
  needs := needs
  needsDecidable := needsDecidable
  registry := registry
  view := view
  granted := granted
  grantedDecidable := grantedDecidable
  PolicyRejected := PolicyRejected
  renderPolicyRejected := renderPolicyRejected
  decide := decide

def rawRevision : RawCall where
  name := choiceSpec.name
  arguments := Codec.bool.encode true

def rawLabel : RawCall where
  name := choiceSpec.name
  arguments := Codec.bool.encode false

def initialWorkspace : Workspace := {
  revision := 7
  label := "proof-carrying"
}

/-- A phase-indexed runner positioned at the first step with no pending calls. -/
def openStep : GenericHarness.Runner config (.step 0 0 []) :=
  ((GenericHarness.Runner.initial config initialWorkspace).beginTurn).beginStep

def allowedRun :
    Except GenericHarness.RunnerError (GenericHarness.Runner.DispatchResult openStep) :=
  openStep.dispatch rawRevision

def rejectedRun :
    Except GenericHarness.RunnerError (GenericHarness.Runner.DispatchResult openStep) :=
  openStep.dispatch rawLabel

def allowedEncodedResult : Option Lean.Json :=
  match allowedRun with
  | .error _ => none
  | .ok result => result.record.encodedResult

def rejectedOutcome : Option GenericHarness.CallOutcome :=
  match rejectedRun with
  | .error _ => none
  | .ok result => some result.record.outcome

def rejectedDispatchCount : Option Nat :=
  match rejectedRun with
  | .error _ => none
  | .ok result => some result.record.dispatchCount

def rejectedModel : Option Workspace :=
  match rejectedRun with
  | .error _ => none
  | .ok result => some result.runner.model

/-- The allowed dependent call returns the `Nat` branch's request-indexed wire encoding. -/
theorem allowed_call_has_typed_encoded_result :
    allowedEncodedResult =
      some (.arr #[.bool true, Codec.nat.encode initialWorkspace.revision]) :=
  rfl

/-- The admitted label request reaches `Config.PolicyRejected`, rather than admission failure. -/
theorem label_call_is_exact_policy_rejection :
    rejectedOutcome =
      some (.policyRejected .deny "label output rejected by exact-call policy") :=
  rfl

/-- Policy rejection contains no dispatch edge, so no provider invocation is required. -/
theorem rejected_call_has_zero_dispatches : rejectedDispatchCount = some 0 :=
  rfl

/-- Rejecting an admitted call preserves the structured model exactly. -/
theorem rejected_call_preserves_model : rejectedModel = some initialWorkspace :=
  rfl

/-- The generic configuration carries a structured model with both numeric and textual state. -/
theorem config_is_not_nat_specialized :
    (GenericHarness.Runner.initial config initialWorkspace).model.label = "proof-carrying" :=
  rfl

end Cordis.Examples.DependentChoice
