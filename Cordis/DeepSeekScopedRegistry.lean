import Cordis.DeepSeekSchemaRegistry
import Cordis.DeepSeekSchemaExecution

/-!
# Scoped, shadowing, and approval-routed schema tools

`DeepSeekSchemaRegistry` gives one finite heterogeneous name registry. The deployed Harness
surface also has lexical registration boundaries: a turn-local declaration may shadow a global
one, a scope may refuse a call without allowing a lower scope to leak through, and a successful
schema admission may still require an explicit approval route before the provider view executes.

This module makes those boundaries intrinsic. Scopes are ordered from nearest to farthest;
lookup stops at the first matching name, including when that entry is restricted. A successful
dispatch retains the selected scope, the schema/generic admission, the approval ticket, and the
dependent provider reply. The approval callback is called before `cfg.view.execute`, so the
type-indexed result cannot witness an execution for a rejected ticket.

The layer remains a pure finite adapter. It does not claim provider discovery, authenticated
scope construction, JavaScript shadowing equivalence, persistence, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekScopedRegistry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Scope data and nearest-name resolution -/

/-- One schema entry together with a pure scope-local restriction.

`none` means that the entry is available. `some reason` denies the entry at the current model;
the reason is retained rather than falling through to a farther scope. -/
structure ScopedEntry
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  entry : SchemaToolEntry cfg
  restriction : Model → Option String

namespace ScopedEntry

def name
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (entry : ScopedEntry cfg) : String :=
  SchemaToolEntry.name entry.entry

end ScopedEntry

/-- A nearest-first lexical scope with unique names inside the scope. -/
structure Scope
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  label : String
  entries : List (ScopedEntry cfg)
  names_nodup : (entries.map ScopedEntry.name).Nodup

/-- A finite lexical environment. `scopes.head` shadows every later scope. -/
structure ScopedRegistry
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  scopes : List (Scope cfg)

private def findEntry
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (entries : List (ScopedEntry cfg))
    (name : String) :
    Option { entry : ScopedEntry cfg // name = entry.name } :=
  match entries with
  | [] => none
  | entry :: rest =>
      if equality : name = entry.name then
        some ⟨entry, equality⟩
      else
        findEntry rest name

theorem findEntry_sound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {entries : List (ScopedEntry cfg)}
    {name : String}
    {found : { entry : ScopedEntry cfg // name = entry.name }}
    (_resolved : findEntry entries name = some found) :
    name = found.val.name :=
  found.property

inductive ResolveError where
  | unknown (name : String)
  | restricted (scope : Nat) (label name reason : String)
deriving BEq, DecidableEq, Repr

/-- The result of a successful nearest-scope lookup. -/
structure ResolvedEntry
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (before : Model)
    (name : String) where
  scope : Nat
  scopeLabel : String
  selected : ScopedEntry cfg
  name_eq : name = selected.name
  unrestricted : selected.restriction before = none

namespace ResolvedEntry

theorem selected_name_eq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {before : Model}
    {name : String}
    (resolved : ResolvedEntry registry before name) :
    name = resolved.selected.name :=
  resolved.name_eq

theorem available
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {before : Model}
    {name : String}
    (resolved : ResolvedEntry registry before name) :
    resolved.selected.restriction before = none :=
  resolved.unrestricted

end ResolvedEntry

private def resolveScopedToolAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (scopes : List (Scope cfg))
    (before : Model)
    (name : String)
    (index : Nat) :
    Except ResolveError (ResolvedEntry registry before name) :=
  match scopes with
  | [] => .error (.unknown name)
  | scope :: rest =>
      match _found : findEntry scope.entries name with
      | none => resolveScopedToolAux registry rest before name (index + 1)
      | some ⟨entry, nameEq⟩ =>
          match restrictionEq : entry.restriction before with
          | some reason => .error (.restricted index scope.label name reason)
          | none =>
              .ok {
                scope := index
                scopeLabel := scope.label
                selected := entry
                name_eq := nameEq
                unrestricted := restrictionEq
              }

/-- Resolve a name in nearest-first scope order. A restricted nearest match is terminal. -/
def resolveScopedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (before : Model)
    (name : String) :
    Except ResolveError (ResolvedEntry registry before name) :=
  resolveScopedToolAux registry registry.scopes before name 0

theorem resolveScopedTool_sound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {before : Model}
    {name : String}
    {resolved : ResolvedEntry registry before name}
    (_resolved : resolveScopedTool registry before name = .ok resolved) :
    name = resolved.selected.name ∧
      resolved.selected.restriction before = none :=
  ⟨resolved.name_eq, resolved.unrestricted⟩

/-! ## Approval-routed dispatch -/

inductive ApprovalRoute where
  | automatic
  | review (queue : String)
deriving BEq, DecidableEq, Repr

inductive ApprovalError where
  | denied (scope : Nat) (name reason : String)
deriving BEq, DecidableEq, Repr

/-- A successful approval is indexed by the exact generic call it authorizes. -/
structure ApprovalTicket
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (call : cfg.Call) where
  route : ApprovalRoute
  note : String

structure ApprovalPolicy
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  approve :
    (before : Model) →
    (scope : Nat) →
    (raw : FunctionCall) →
    (call : cfg.Call) →
    Except ApprovalError (ApprovalTicket call)

inductive DispatchError where
  | resolve (error : ResolveError)
  | execution (error : ExecutionError)
  | approval (error : ApprovalError)
deriving BEq, DecidableEq, Repr

/-- A successful scoped call retains the approval proof and dependent execution evidence. -/
structure ScopedExecutedCall
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    {before : Model}
    {raw : FunctionCall}
    (resolved : ResolvedEntry registry before raw.name)
    (call : cfg.Call) where
  ticket : ApprovalTicket call
  executed : ExecutedCall resolved.selected.entry.binding raw before call

namespace ScopedExecutedCall

def after
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {raw : FunctionCall}
    {resolved : ResolvedEntry registry before raw.name}
    {call : cfg.Call}
    (result : ScopedExecutedCall registry approval resolved call) : Model :=
  result.executed.reply.value.after

theorem selected_name_eq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {raw : FunctionCall}
    {resolved : ResolvedEntry registry before raw.name}
    {call : cfg.Call}
    (_result : ScopedExecutedCall registry approval resolved call) :
    raw.name = resolved.selected.name :=
  resolved.name_eq

theorem provider_execution_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {raw : FunctionCall}
    {resolved : ResolvedEntry registry before raw.name}
    {call : cfg.Call}
    (result : ScopedExecutedCall registry approval resolved call) :
    cfg.view.execute call = .ok result.executed.reply :=
  result.executed.execution

end ScopedExecutedCall

def dispatchScopedCall
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (before : Model)
    (raw : FunctionCall) :
    Except DispatchError
      (Sigma fun resolved : ResolvedEntry registry before raw.name =>
        Sigma fun call : cfg.Call =>
          ScopedExecutedCall registry approval resolved call) :=
  match _resolveEq : resolveScopedTool registry before raw.name with
  | .error error => .error (.resolve error)
  | .ok resolved =>
      match _admissionEq : validateAndAdmit resolved.selected.entry.binding before raw with
      | .error error => .error (.execution (.admission error))
      | .ok ⟨call, checked⟩ =>
          let genericRaw : RawCall := {
            name := raw.name
            arguments := checked.provider.arguments.json
          }
          match policyEq : cfg.decide before genericRaw call with
          | .reject decision _ reason =>
              .error (.execution (.policy decision (cfg.renderPolicyRejected call reason)))
          | .allow =>
              match _approvalEq : approval.approve before resolved.scope raw call with
              | .error error => .error (.approval error)
              | .ok ticket =>
                  match executionEq : cfg.view.execute call with
                  | .error message => .error (.execution (.provider message))
                  | .ok reply =>
                      .ok ⟨resolved, ⟨call, {
                        ticket
                        executed := {
                          checked
                          reply
                          policy := policyEq
                          execution := executionEq
                        }
                      }⟩⟩

/-! ## Executable scope/approval fixture -/

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example

def scopedRegistry
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    ScopedRegistry dualConfig := {
  scopes := [
    {
      label := "turn-local"
      entries := [{
        entry := {
          tool := DeepSeekApi.exampleTool
          binding := dualWeatherBinding weatherCertificate
        }
        restriction := fun before =>
          if before = 0 then none else some "turn-local approval required"
      }]
      names_nodup := by
        simp [ScopedEntry.name, SchemaToolEntry.name, DeepSeekApi.exampleTool]
    },
    {
      label := "global"
      entries := [
        {
          entry := {
            tool := DeepSeekApi.exampleTool
            binding := dualWeatherBinding weatherCertificate
          }
          restriction := fun _ => none
        },
        {
          entry := {
            tool := clockTool
            binding := dualClockBinding clockCertificate
          }
          restriction := fun _ => none
        }
      ]
      names_nodup := by
        simp [ScopedEntry.name, SchemaToolEntry.name, DeepSeekApi.exampleTool, clockTool]
    }
  ]
}

def approvalPolicy : ApprovalPolicy dualConfig where
  approve := fun _ scope _ _ =>
    if scope = 0 then
      .ok { route := .automatic, note := "turn-local" }
    else
      .ok { route := .review "global-tools", note := "global" }

def rejectingApproval : ApprovalPolicy dualConfig where
  approve := fun _ scope raw _ =>
    .error (.denied scope raw.name "explicit approval required")

def clockCall : FunctionCall where
  id := "call-clock-0"
  name := "get_time"
  arguments := "{\"city\":\"New York\"}"

def shadowedWeather : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match resolveScopedTool (scopedRegistry weatherCertificate clockCertificate) 0
          "get_weather" with
      | .ok resolved => resolved.scope == 0 && resolved.scopeLabel == "turn-local"
      | .error _ => false
  | _, _ => false

def restrictedWeather : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match resolveScopedTool (scopedRegistry weatherCertificate clockCertificate) 1
          "get_weather" with
      | .error (.restricted 0 "turn-local" "get_weather"
          "turn-local approval required") => true
      | _ => false
  | _, _ => false

def globalClock : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dispatchScopedCall (scopedRegistry weatherCertificate clockCertificate)
          approvalPolicy 0 clockCall with
      | .ok ⟨resolved, ⟨_, result⟩⟩ =>
          resolved.scope == 1 && result.ticket.route == .review "global-tools" &&
            result.executed.reply.value.after == 0
      | .error _ => false
  | _, _ => false

def approvalRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dispatchScopedCall (scopedRegistry weatherCertificate clockCertificate)
          rejectingApproval 0 DeepSeekToolAdmission.weatherCall with
      | .error (.approval (.denied 0 "get_weather" "explicit approval required")) => true
      | _ => false
  | _, _ => false

def unknownRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      let unknown : FunctionCall := {
        id := "call-unknown-0"
        name := "not_registered"
        arguments := "{}"
      }
      match dispatchScopedCall (scopedRegistry weatherCertificate clockCertificate)
          approvalPolicy 0 unknown with
      | .error (.resolve (.unknown "not_registered")) => true
      | _ => false
  | _, _ => false

end Example

end Cordis.DeepSeekScopedRegistry
