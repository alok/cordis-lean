import Cordis.Api

/-!
# Proof-carrying tool contracts

Tool contracts make preconditions, authority, outcomes, and postconditions part
of the operation's type. A real backend may return observations, but only a
verified implementation can construct `CertifiedOutcome` for the pure kernel.
-/

namespace Cordis

universe u

/-- How a tool's effects relate to the recoverable system boundary. -/
inductive EmissionClass where
  | pure
  | internalReversible
  | externalIdempotent
  | compensatable
  | irreversible
deriving BEq, DecidableEq, Repr

/-- A request-indexed tool contract over an abstract model state. -/
structure ToolSpec (Model Capability : Type u) where
  name : String
  description : String
  Input : Type u
  Output : Input -> Type u
  Failure : Input -> Type u
  pre : Input -> Model -> Prop
  post : (input : Input) ->
    Model -> Except (Failure input) (Output input) -> Model -> Prop
  required : Input -> Capability -> Prop
  emission : EmissionClass

namespace ToolSpec

/-- All capabilities required by an input are present in `granted`. -/
def Authorized
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability)
    (input : spec.Input)
    (granted : Capability -> Prop) : Prop :=
  forall capability, spec.required input capability -> granted capability

/-- A request that has passed precondition and capability checking. -/
structure Invocation
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability) where
  input : spec.Input
  before : Model
  granted : Capability -> Prop
  precondition : spec.pre input before
  authorized : spec.Authorized input granted

/-- A result and successor model carrying the tool's postcondition proof. -/
structure CertifiedOutcome
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability)
    (invocation : Invocation spec) where
  result : Except (spec.Failure invocation.input) (spec.Output invocation.input)
  after : Model
  postcondition : spec.post invocation.input invocation.before result after

/-- A pure tool implementation that discharges its declared contract. -/
structure VerifiedTool
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability) where
  execute : (invocation : Invocation spec) -> CertifiedOutcome spec invocation

end ToolSpec

/-- A heterogeneous catalog of dependent tool contracts. -/
structure ToolCatalog (Model Capability : Type u) where
  Tool : Type u
  toolDecEq : DecidableEq Tool
  spec : Tool -> ToolSpec Model Capability

attribute [instance] ToolCatalog.toolDecEq

namespace ToolCatalog

/-- The catalog interpreted as the generic dependent CORDIS API. -/
def signature
    {Model Capability : Type u}
    (catalog : ToolCatalog Model Capability) : Signature where
  Op := catalog.Tool
  opDecEq := catalog.toolDecEq
  Request tool := ToolSpec.Invocation (catalog.spec tool)
  Response tool invocation := ToolSpec.CertifiedOutcome (catalog.spec tool) invocation

/-- Adapt a verified tool into a provider for its catalog operation. -/
def provider
    {Model Capability : Type u}
    (catalog : ToolCatalog Model Capability)
    (tool : catalog.Tool)
    (id : ProviderId)
    (implementation : ToolSpec.VerifiedTool (catalog.spec tool)) :
    Provider catalog.signature tool where
  id := id
  handle invocation := .ok (implementation.execute invocation)

end ToolCatalog

/-- A policy result ordered from most permissive to most restrictive. -/
inductive Decision where
  | allow
  | ask
  | deny
deriving BEq, DecidableEq, Repr

namespace Decision

/-- Combine two guards without allowing either guard to restore authority. -/
def tighten : Decision -> Decision -> Decision
  | .deny, _ | _, .deny => .deny
  | .ask, _ | _, .ask => .ask
  | .allow, .allow => .allow

@[simp]
theorem tighten_deny_left (decision : Decision) : tighten .deny decision = .deny := by
  cases decision <;> rfl

@[simp]
theorem tighten_deny_right (decision : Decision) : tighten decision .deny = .deny := by
  cases decision <;> rfl

@[simp]
theorem tighten_allow_left (decision : Decision) : tighten .allow decision = decision := by
  cases decision <;> rfl

@[simp]
theorem tighten_allow_right (decision : Decision) : tighten decision .allow = decision := by
  cases decision <;> rfl

theorem tighten_commutative (left right : Decision) :
    tighten left right = tighten right left := by
  cases left <;> cases right <;> rfl

theorem tighten_associative (first second third : Decision) :
    tighten (tighten first second) third = tighten first (tighten second third) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem tighten_idempotent (decision : Decision) : tighten decision decision = decision := by
  cases decision <;> rfl

/-- Once any policy guard denies a call, the combined decision cannot allow it. -/
theorem denied_never_allows
    (prior guard : Decision)
    (denied : prior = .deny ∨ guard = .deny) :
    tighten prior guard ≠ .allow := by
  cases prior <;> cases guard <;> simp_all [tighten]

end Decision

end Cordis
