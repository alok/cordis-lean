import Cordis.DeepSeekExternalToolProcess
import Cordis.Session

/-!
# Process-backed dependent tool rounds

`DeepSeekExternalToolProcess` stops at a certified model outcome.  This module
adds the next local boundary: the accepted outcome is paired with the exact
two-event `Session` append that records the call and exposes its result.  The
session endpoint is not an untyped list append: `Session.ValidLog` proves the
log-only call, the earlier-reference citation, the surface projection, and the
sequence-number discipline.

The renderer is intentionally supplied by the caller.  A process observation
therefore does not smuggle a provider-specific wire format into the session;
the only model-state claim is still `ToolSpec.post` carried by
`AcceptedResult.certified`.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekExternalToolRound

open Cordis
open Cordis.Session
open Cordis.DeepSeekExternalToolProcess

universe u

/-- How a typed external result is rendered into the model-visible result event. -/
structure SurfaceCodec
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability} where
  render : (input : spec.Input) ->
    Except (spec.Failure input) (spec.Output input) -> String
  isError : (input : spec.Input) ->
    Except (spec.Failure input) (spec.Output input) -> Bool

/-- The ordinary rendering for a successful or failed result. -/
def defaultSurfaceCodec
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability} : SurfaceCodec (spec := spec) where
  render := fun _ result =>
    match result with
    | .ok _ => "ok"
    | .error _ => "error"
  isError := fun _ result =>
    match result with
    | .ok _ => false
    | .error _ => true

/-- Append a log-only call and then its cited model-visible result. -/
def appendToolRound
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (_accepted : AcceptedResult observed)
    (surface : SurfaceCodec (spec := spec))
    (session : Session noExtensions)
    (turn step : Nat)
    (call : ToolCall) : Session noExtensions :=
  let withCall := session.appendLogOnly .toolCall {
    turn := turn
    step := step
    call := call
  }
  have sourceEarlier : session.nextSeq < withCall.nextSeq := by
    dsimp [withCall, Session.appendLogOnly, Session.append]
    omega
  withCall.appendSurface .toolResult {
    turn := turn
    step := step
    callId := call.id
    content := surface.render invocation.input observed.result
    isError := surface.isError invocation.input observed.result
  } [session.nextSeq] (by simp)
    (by
      intro source member
      simp at member
      subst source
      exact sourceEarlier)

/-- A process-backed result together with its exact append-only session endpoint. -/
structure ExternalToolRound
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (accepted : AcceptedResult observed) where
  before : Session noExtensions
  turn : Nat
  step : Nat
  call : ToolCall
  call_name : call.name = spec.name
  surface : SurfaceCodec (spec := spec)
  after : Session noExtensions
  after_eq : after = appendToolRound accepted surface before turn step call

namespace ExternalToolRound

def certified
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (_round : ExternalToolRound accepted) :
    ToolSpec.CertifiedOutcome spec invocation :=
  accepted.certified

theorem certified_postcondition
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (round : ExternalToolRound accepted) :
    spec.post invocation.input invocation.before observed.result
      round.certified.after :=
  round.certified.postcondition

theorem after_nextSeq
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (round : ExternalToolRound accepted) :
    round.after.nextSeq = round.before.nextSeq + 2 := by
  rw [round.after_eq]
  simp [appendToolRound, Session.appendSurface, Session.appendLogOnly, Session.append]

theorem after_messages
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (round : ExternalToolRound accepted) :
    round.after.messages = round.before.messages ++ [
      .toolResult round.call.id
        (round.surface.render invocation.input observed.result)
        (round.surface.isError invocation.input observed.result)] := by
  rw [round.after_eq]
  simp [appendToolRound, Session.appendSurface, Session.appendLogOnly, Session.append,
    Session.messages, deriveMessages]

theorem after_protocolProjection
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (round : ExternalToolRound accepted) :
    protocolProjection round.after.events =
      protocolProjection round.before.events ++ [
        .toolCall round.turn round.step round.call.id,
        .toolResult round.turn round.step round.call.id] := by
  rw [round.after_eq]
  simp [appendToolRound, Session.appendSurface, Session.appendLogOnly,
    Session.append, protocolProjection, LoggedEvent.protocolEvent?]

theorem call_name_exact
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    (round : ExternalToolRound accepted) :
    round.call.name = spec.name :=
  round.call_name

end ExternalToolRound

/-! ## A concrete dependent process/session witness -/

def echoCall : ToolCall where
  id := ⟨19⟩
  name := echoSpec.name
  arguments := "hello from cordis"

def echoSurface : SurfaceCodec (spec := echoSpec) where
  render := fun _ result =>
    match result with
    | .ok value => value
    | .error _ => "error"
  isError := fun _ result =>
    match result with
    | .ok _ => false
    | .error _ => true

theorem echoCall_name : echoCall.name = echoSpec.name := rfl

end Cordis.DeepSeekExternalToolRound
