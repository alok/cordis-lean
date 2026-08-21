import Cordis.DeepSeekToolSchema

/-!
# Certified DeepSeek function-call admission

`DeepSeekApi.FunctionCall` intentionally preserves a provider call name and raw argument text.
`DeepSeekToolSchema` certifies a declared tool and its bounded object schema, but those two
certificates are useful together only when the call name is tied to the declaration. This module
supplies that small bridge: a successful `validateFunctionCall` proves exact name agreement and
stores the parsed, primitive-checked argument certificate.

This is an admission boundary before generic capability execution. It does not claim that a
provider obeyed the schema, that the call ID is authentic, that a `GenericHarness.Config` has a
corresponding capability, or that the deployed DeepSeek Harness has these semantics.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekToolAdmission

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekToolSchema

inductive FunctionCallSchemaError where
  | nameMismatch (id : String) (actual expected : String)
  | arguments (id name : String) (error : ArgumentError)
deriving BEq, DecidableEq, Repr

structure CertifiedFunctionCall {tool : ToolDefinition}
    (certificate : ValidatedToolDefinition tool)
    (raw : FunctionCall) where
  name_eq : raw.name = tool.function.name
  arguments : ValidatedArguments certificate.parameters raw.arguments

def validateFunctionCall {tool : ToolDefinition}
    (certificate : ValidatedToolDefinition tool)
    (raw : FunctionCall) :
    Except FunctionCallSchemaError (CertifiedFunctionCall certificate raw) :=
  if name_eq : raw.name = tool.function.name then
    match certificate.validateArguments raw.arguments with
    | .error error => .error (.arguments raw.id raw.name error)
    | .ok arguments => .ok { name_eq, arguments }
  else
    .error (.nameMismatch raw.id raw.name tool.function.name)

theorem CertifiedFunctionCall.call_name_eq {tool : ToolDefinition}
    {certificate : ValidatedToolDefinition tool}
    {raw : FunctionCall}
    (call : CertifiedFunctionCall certificate raw) :
    raw.name = tool.function.name :=
  call.name_eq

theorem CertifiedFunctionCall.arguments_parse_eq {tool : ToolDefinition}
    {certificate : ValidatedToolDefinition tool}
    {raw : FunctionCall}
    (call : CertifiedFunctionCall certificate raw) :
    Lean.Json.parse raw.arguments = .ok call.arguments.json :=
  call.arguments.parsed_eq

def weatherCall : FunctionCall where
  id := "call-weather-0"
  name := "get_weather"
  arguments := "{\"city\":\"San Francisco\"}"

def weatherCallWrongName : FunctionCall where
  id := "call-weather-0"
  name := "wrong_tool"
  arguments := "{\"city\":\"San Francisco\"}"

def weatherCallWrongArguments : FunctionCall where
  id := "call-weather-0"
  name := "get_weather"
  arguments := "{\"city\":3}"

def weatherCallAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match validateFunctionCall certificate weatherCall with
      | .ok _ => true
      | .error _ => false

def weatherCallWrongNameRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match validateFunctionCall certificate weatherCallWrongName with
      | .ok _ => false
      | .error _ => true

def weatherCallWrongArgumentsRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match validateFunctionCall certificate weatherCallWrongArguments with
      | .ok _ => false
      | .error _ => true

end Cordis.DeepSeekToolAdmission
