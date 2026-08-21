import Cordis.DeepSeekToolAdmission
import Cordis.GenericHarness

/-!
# Provider-schema to generic-call admission

`DeepSeekToolAdmission` proves that one provider function call matches one
bounded `ToolDefinition`. `GenericHarness.Config.validate` proves a second,
dependent admission against the local catalog, needs predicate, codecs, and
contract. This module composes those checks while keeping both certificates.

The two tool vocabularies are intentionally not identified definitionally: a
provider schema is wire metadata, while a generic `ToolSpec` carries typed
preconditions, postconditions, capabilities, and a provider view. A
`SchemaToolBinding` therefore supplies the explicit name correspondence. A
successful `validateAndAdmit` returns an existentially indexed generic call,
so its request and response types remain selected by the generic catalog.
Execution, provider identity, and equivalence with the remote provider's
schema semantics remain outside this bridge.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekGenericBridge

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

universe u

/-- The two explicit failures exposed by the composed admission boundary. -/
inductive BridgeError where
  | schema (error : FunctionCallSchemaError)
  | generic (error : AdmissionError)
deriving BEq, DecidableEq, Repr

/-- A provider declaration bound to one generic catalog operation by name. -/
structure SchemaToolBinding
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (tool : ToolDefinition) where
  certificate : ValidatedToolDefinition tool
  genericTool : cfg.catalog.Tool
  name_eq : tool.function.name = (cfg.catalog.spec genericTool).name

/-- A successful provider/schema check plus generic dependent admission. -/
structure SchemaCheckedCall
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (raw : FunctionCall)
    (before : Model)
    (call : cfg.Call) where
  provider : CertifiedFunctionCall binding.certificate raw
  validation : cfg.validate before {
      name := raw.name
      arguments := provider.arguments.json
    } = .ok call

/-- The provider name is the name bound to the generic catalog operation. -/
theorem SchemaCheckedCall.provider_name_eq
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (checked : SchemaCheckedCall binding raw before call) :
    raw.name = (cfg.catalog.spec binding.genericTool).name := by
  exact checked.provider.name_eq.trans binding.name_eq

/--
Run provider-schema admission and then generic admission on the exact parsed
JSON AST retained by the first certificate. The result is an existential
generic call because the selected request type depends on the resolved tool.
-/
def validateAndAdmit
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (raw : FunctionCall) :
    Except BridgeError
      (Sigma fun call : cfg.Call => SchemaCheckedCall binding raw before call) :=
  match validateFunctionCall binding.certificate raw with
  | .error error => .error (.schema error)
  | .ok provider =>
      let genericRaw : RawCall := {
        name := raw.name
        arguments := provider.arguments.json
      }
      match validation : cfg.validate before genericRaw with
      | .error error => .error (.generic error)
      | .ok call => .ok ⟨call, { provider, validation }⟩

theorem validateAndAdmit_provider_name_eq
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    {before : Model}
    {raw : FunctionCall}
    {call : cfg.Call}
    (checked : SchemaCheckedCall binding raw before call) :
    raw.name = (cfg.catalog.spec binding.genericTool).name :=
  checked.provider_name_eq

theorem validateAndAdmit_generic_tool_eq
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    {before : Model}
    {raw : FunctionCall}
    {call : cfg.Call}
    (checked : SchemaCheckedCall binding raw before call) :
    call.op = binding.genericTool := by
  have resolve_eq : cfg.wire.resolve raw.name = some binding.genericTool := by
    rw [checked.provider.name_eq.trans binding.name_eq]
    exact cfg.wire.resolve_name binding.genericTool
  have validation := checked.validation
  unfold Config.validate ToolWire.validate at validation
  rw [resolve_eq] at validation
  cases needs_result : cfg.needsDecidable binding.genericTool with
  | isFalse notDeclared =>
      simp [needs_result] at validation
  | isTrue declared =>
      cases decode_result :
          (cfg.wire.inputCodec binding.genericTool).decode checked.provider.arguments.json with
      | error decodeError =>
          simp [needs_result, decode_result] at validation
      | ok input =>
          cases admission_result : cfg.wire.certifyAdmission binding.genericTool input before
              (cfg.granted before {
                name := raw.name
                arguments := checked.provider.arguments.json
              })
              (cfg.grantedDecidable before {
                name := raw.name
                arguments := checked.provider.arguments.json
              }) with
          | error reason =>
              simp [needs_result, decode_result, admission_result] at validation
          | ok evidence =>
              simp [needs_result, decode_result, admission_result] at validation
              have op_eq := congrArg
                (fun selected => selected.op)
                validation
              simpa using op_eq.symm

/-! ## A small executable bridge fixture -/

namespace Example

inductive Capability where
  | invoke
deriving BEq, DecidableEq, Repr

inductive Operation where
  | weather
deriving BEq, DecidableEq, Repr

def weatherSpec : ToolSpec Nat Capability where
  name := "get_weather"
  description := "Accept a certified weather request"
  Input := Lean.Json
  Output _ := String
  Failure _ := String
  pre _ _ := True
  post _ before _ after := after = before
  required _ capability := capability = .invoke
  emission := .externalIdempotent

def weatherCatalog : ToolCatalog Nat Capability where
  Tool := Operation
  toolDecEq := inferInstance
  spec
    | .weather => weatherSpec

def weatherImplementation :
    ToolSpec.VerifiedTool (weatherCatalog.spec .weather) where
  execute invocation := {
    result := .ok "accepted"
    after := invocation.before
    postcondition := rfl
  }

def weatherProvider : Provider weatherCatalog.signature .weather :=
  weatherCatalog.provider .weather
    { domain := "example.deepseek"
      name := "weather"
      major := 1 }
    weatherImplementation

def weatherRegistry : Registry weatherCatalog.signature
  | .weather => some weatherProvider

def weatherView : View weatherCatalog.signature weatherRegistry
    (fun _ => True) where
  resolve operation _ := by
    cases operation
    exact { provider := weatherProvider, present := rfl }

def jsonObjectCodec : Codec Lean.Json where
  schema := Lean.Json.mkObj [("type", .str "object")]
  encode value := value
  decode value := .ok value
  roundtrip := by intro value; rfl

def weatherWire : ToolWire weatherCatalog where
  resolve
    | "get_weather" => some .weather
    | _ => none
  resolve_name tool := by cases tool <;> rfl
  inputCodec _ := jsonObjectCodec
  outputCodec _ _ := Codec.string
  failureCodec _ _ := Codec.string
  certifyAdmission _ _ _ granted grantedDecidable :=
    match grantedDecidable .invoke with
    | .isFalse _ => .error "weather capability is not granted"
    | .isTrue hasInvoke =>
        .ok {
          precondition := trivial
          authorized := by
            intro capability required
            change capability = Capability.invoke at required
            subst capability
            exact hasInvoke
        }

def weatherConfig : GenericHarness.Config Nat Capability where
  catalog := weatherCatalog
  wire := weatherWire
  needs := fun _ => True
  needsDecidable := fun _ => isTrue trivial
  registry := weatherRegistry
  view := weatherView
  granted := fun _ _ _ => True
  grantedDecidable := fun _ _ _ => isTrue trivial
  PolicyRejected := fun _ => String
  renderPolicyRejected := fun _ reason => reason
  decide := fun _ _ _ => .allow

def weatherBinding
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    SchemaToolBinding weatherConfig DeepSeekApi.exampleTool where
  certificate := certificate
  genericTool := .weather
  name_eq := rfl

def weatherAdmitted
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    Except BridgeError
      (Sigma fun call : weatherConfig.Call =>
        SchemaCheckedCall (weatherBinding certificate)
          DeepSeekToolAdmission.weatherCall 0 call) :=
  validateAndAdmit (weatherBinding certificate) 0
    DeepSeekToolAdmission.weatherCall

def weatherAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherAdmitted certificate with
      | .error _ => false
      | .ok _ => true

end Example

end Cordis.DeepSeekGenericBridge
