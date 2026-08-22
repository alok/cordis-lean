import Cordis.DeepSeekProviderStreamAssembly
import Cordis.DeepSeekScopedRegistry
import Cordis.DeepSeekAssemblerToolRound
import Cordis.DeepSeekSchemaStreamConversation

/-!
# Scoped streamed tool round

This module composes the source-shaped provider stream with the scoped/approval-routed
schema registry.  A successful round keeps the provider assembly certificate, the nearest
scope chosen for every call, the approval ticket, the dependent execution reply, and the
session append endpoint in one indexed package.  The execution trace is indexed by the
model before and after each call, so a result for a rejected or differently scoped call
cannot be attached to the successful endpoint.

The bridge is a finite local adapter.  It does not claim provider call-ID authenticity,
external tool effects, scope-construction equivalence, persistence, cancellation, or
deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekScopedStreamToolRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekSchemaRegistry
open Cordis.GenericHarness

/-! ## Dependent scoped execution trace -/

inductive ScopedExecutionTrace
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg) :
    (before : Model) → List FunctionCall → (after : Model) → Type where
  | nil (before : Model) :
      ScopedExecutionTrace registry approval before [] before
  | cons
      {before after final : Model}
      {raw : FunctionCall}
      {rest : List FunctionCall}
      (resolved : ResolvedEntry registry before raw.name)
      (call : cfg.Call)
      (head : ScopedExecutedCall registry approval resolved call)
      (tail : ScopedExecutionTrace registry approval head.after rest final) :
      ScopedExecutionTrace registry approval before (raw :: rest) final

namespace ScopedExecutionTrace

def toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {raw : FunctionCall}
    {resolved : ResolvedEntry registry before raw.name}
    {call : cfg.Call}
    (head : ScopedExecutedCall registry approval resolved call) :
    ExecutedTool cfg where
  raw := raw
  before := before
  parsed := head.executed.checked.provider.arguments.json
  parsed_eq := head.executed.checked.provider.arguments.parsed_eq
  call := call
  validation := head.executed.checked.validation
  reply := head.executed.reply
  policy := head.executed.policy
  execution := head.executed.execution

def toExecutedTools
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {calls : List FunctionCall} :
    ScopedExecutionTrace registry approval before calls after → List (ExecutedTool cfg)
  | .nil _ => []
  | .cons _ _ head tail =>
      toExecutedTool head :: toExecutedTools tail

def length
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {calls : List FunctionCall} :
    ScopedExecutionTrace registry approval before calls after → Nat
  | .nil _ => 0
  | .cons _ _ _ tail => length tail + 1

theorem toExecutedTools_length
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {calls : List FunctionCall}
    (trace : ScopedExecutionTrace registry approval before calls after) :
    (toExecutedTools trace).length = calls.length := by
  induction trace with
  | nil => rfl
  | cons resolved call head tail ih =>
      simp [toExecutedTools, ih]

theorem length_eq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {calls : List FunctionCall}
    (trace : ScopedExecutionTrace registry approval before calls after) :
    length trace = calls.length := by
  induction trace with
  | nil => rfl
  | cons resolved call head tail ih =>
      simp [length, ih]

end ScopedExecutionTrace

/-! ## Call execution -/

inductive ScopedStreamToolRoundError where
  | assembly (error : ProviderStreamError)
  | dispatch (error : DispatchError)
deriving DecidableEq, Repr

def executeScopedCalls
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (before : Model)
    (calls : List FunctionCall) :
    Except DispatchError
      (Sigma fun after : Model =>
        ScopedExecutionTrace registry approval before calls after) :=
  match calls with
  | [] => .ok ⟨before, .nil before⟩
  | raw :: rest =>
      match dispatchScopedCall registry approval before raw with
      | .error error => .error error
      | .ok ⟨resolved, ⟨call, head⟩⟩ =>
      match executeScopedCalls registry approval head.after rest with
          | .error error => .error error
          | .ok ⟨after, tail⟩ =>
              .ok ⟨after, .cons (after := after) resolved call head tail⟩

structure ScopedStreamToolRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (before : Model)
    (body : String)
    (after : Model) where
  source : ValidatedProviderAssembly body
  source_eq : validateBody body = .ok source
  calls : List FunctionCall
  calls_eq : calls = toFunctionCalls source.assembly.result
  execution : ScopedExecutionTrace registry approval before calls after

def executeBodyScopedTools
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (before : Model)
    (body : String) :
    Except ScopedStreamToolRoundError
      (Sigma fun after : Model => ScopedStreamToolRound registry approval before body after) :=
  match sourceEq : validateBody body with
  | .error error => .error (.assembly error)
  | .ok source =>
      let calls := toFunctionCalls source.assembly.result
      match _dispatchEq : executeScopedCalls registry approval before calls with
      | .error error => .error (.dispatch error)
      | .ok ⟨after, execution⟩ =>
          .ok ⟨after, {
            source
            source_eq := sourceEq
            calls
            calls_eq := rfl
            execution
          }⟩

theorem ScopedStreamToolRound.source_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {body : String}
    {after : Model}
    (round : ScopedStreamToolRound registry approval before body after) :
    validateBody body = .ok round.source :=
  round.source_eq

theorem ScopedStreamToolRound.calls_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {body : String}
    {after : Model}
    (round : ScopedStreamToolRound registry approval before body after) :
    round.calls = toFunctionCalls round.source.assembly.result :=
  round.calls_eq

/-! ## Session append -/

def appendRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ScopedStreamToolRound registry approval before body after)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  let assistant := appendAssistant session turn step round.source.assembly.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  appendExecutedToolResults assistant turn step 0 session.nextSeq
    (ScopedExecutionTrace.toExecutedTools round.execution) (by
      change session.nextSeq < assistant.nextSeq
      simp [assistant, appendAssistant, StreamSession.appendAssistant,
        StreamSession.toAssistantPayload, Session.Session.appendSurface,
        Session.Session.append])

theorem appendRound_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ScopedStreamToolRound registry approval before body after)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendRound session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).messages =
      session.messages ++
        [.assistant (toAssistantView round.source.assembly.result).content
          (StreamSession.toSessionToolCalls (toAssistantView round.source.assembly.result)
            (DeepSeekSessionRunner.sequentialAssignment 0
              (toAssistantView round.source.assembly.result)))] ++
        executedToolMessages 0 (ScopedExecutionTrace.toExecutedTools round.execution) := by
  let assistant := appendAssistant session turn step round.source.assembly.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  have assistant_messages := appendAssistant_messages session turn step
    round.source.assembly.result sourceEventSeqs sourcesNodup sourcesEarlier
  have assistant_next : session.nextSeq < assistant.nextSeq := by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append]
  have tool_messages := appendExecutedToolResults_messages assistant turn step 0
    session.nextSeq (ScopedExecutionTrace.toExecutedTools round.execution) assistant_next
  change (appendExecutedToolResults assistant turn step 0 session.nextSeq
      (ScopedExecutionTrace.toExecutedTools round.execution) assistant_next).messages = _
  rw [tool_messages, assistant_messages]

theorem appendRound_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before after : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ScopedStreamToolRound registry approval before body after)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendRound session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).nextSeq =
      session.nextSeq + 1 + round.calls.length := by
  have assistant_next : session.nextSeq + 1 =
      (appendAssistant session turn step round.source.assembly.result
        sourceEventSeqs sourcesNodup sourcesEarlier).nextSeq := by
    change session.nextSeq + 1 = _
    rfl
  have trace_length := ScopedExecutionTrace.toExecutedTools_length round.execution
  have round_length :
      (ScopedExecutionTrace.toExecutedTools round.execution).length = round.calls.length := by
    simpa [round.calls_eq] using trace_length
  calc
    (appendRound session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).nextSeq =
        (appendAssistant session turn step round.source.assembly.result
          sourceEventSeqs sourcesNodup sourcesEarlier).nextSeq +
          (ScopedExecutionTrace.toExecutedTools round.execution).length := by
      unfold appendRound
      rw [appendExecutedToolResults_nextSeq]
    _ = session.nextSeq + 1 + round.calls.length := by
      rw [← assistant_next, round_length]

/-! ## Executable scoped/shadowing/approval fixture -/

namespace Example

open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekToolSchema

def scopedDualRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    Except ScopedStreamToolRoundError
      (Sigma fun after : Nat =>
        ScopedStreamToolRound
          (scopedRegistry weatherCertificate clockCertificate)
          approvalPolicy 0 dualToolStreamBody after) :=
  executeBodyScopedTools (scopedRegistry weatherCertificate clockCertificate)
    approvalPolicy 0 dualToolStreamBody

def scopedDualRoundSummary : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match scopedDualRound weatherCertificate clockCertificate with
      | .error _ => false
      | .ok ⟨after, round⟩ =>
          after == 0 && round.calls.length == 2 &&
            (ScopedExecutionTrace.toExecutedTools round.execution).length == 2
  | _, _ => false

def scopedDualSessionSummary : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match scopedDualRound weatherCertificate clockCertificate with
      | .error _ => false
      | .ok ⟨_, round⟩ =>
          let session := appendRound (Session.Session.empty Session.noExtensions) 1 0 round []
            (by simp) (by simp)
          session.messages.length == 3 && session.nextSeq == 3
  | _, _ => false

def restrictedShadowRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dispatchScopedCall (scopedRegistry weatherCertificate clockCertificate)
          approvalPolicy 1 DeepSeekToolAdmission.weatherCall with
      | .error (.resolve (.restricted 0 "turn-local" "get_weather"
          "turn-local approval required")) => true
      | _ => false
  | _, _ => false

def explicitApprovalRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dispatchScopedCall (scopedRegistry weatherCertificate clockCertificate)
          rejectingApproval 0 DeepSeekToolAdmission.weatherCall with
      | .error (.approval (.denied 0 "get_weather" "explicit approval required")) => true
      | _ => false
  | _, _ => false

end Example

end Cordis.DeepSeekScopedStreamToolRound
