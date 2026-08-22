import Cordis.DeepSeekAssemblerToolRound
import Cordis.DeepSeekProviderStreamAssembly

/-!
# Wire-backed dependent tool round

This is the first complete local composition from strict DeepSeek SSE text through
provider-shaped assembly into dependent tool execution.  The stream validator and
rich projection retain their own wire/trace certificates; the provider assembler
retains a second exact fold certificate; and the dependent execution certificate
retains the model-indexed call list and replies.

The executable example uses an in-memory strict SSE body rather than network I/O.  It
does not claim credential, external-effect, persistence, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamToolRound

open Cordis
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderStreamAssembly

inductive StreamToolRoundError where
  | assembly (error : ProviderStreamError)
  | execution (error : ToolRoundError)
deriving DecidableEq, Repr

structure ValidatedStreamToolRound
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  source : ValidatedProviderAssembly body
  source_eq : validateBody body = .ok source
  execution : ExecutionCertificate cfg before source.assembly.result
  execution_eq :
    executeAssembledTools cfg before source.assembly.result = .ok execution

def executeBodyTools
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) :
    Except StreamToolRoundError (ValidatedStreamToolRound cfg before body) :=
  match sourceEq : validateBody body with
  | .error error => .error (.assembly error)
  | .ok source =>
      match executionEq :
          executeAssembledTools cfg before source.assembly.result with
      | .error error => .error (.execution error)
      | .ok execution => .ok {
          source
          source_eq := sourceEq
          execution
          execution_eq := executionEq
        }

theorem ValidatedStreamToolRound.source_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : ValidatedStreamToolRound cfg before body) :
    validateBody body = .ok round.source :=
  round.source_eq

theorem ValidatedStreamToolRound.execution_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : ValidatedStreamToolRound cfg before body) :
    executeAssembledTools cfg before round.source.assembly.result = .ok round.execution :=
  round.execution_eq

def appendRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ValidatedStreamToolRound cfg before body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  let assistant := appendAssistant session turn step round.source.assembly.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  appendToolResults assistant turn step session.nextSeq round.execution (by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append])

theorem appendRound_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ValidatedStreamToolRound cfg before body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendRound session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).messages =
      session.messages ++
        [.assistant (toAssistantView round.source.assembly.result).content
          (StreamSession.toSessionToolCalls
            (toAssistantView round.source.assembly.result)
            (DeepSeekSessionRunner.sequentialAssignment 0
              (toAssistantView round.source.assembly.result)))] ++
        executedToolMessages 0 round.execution.executions := by
  let assistant := appendAssistant session turn step round.source.assembly.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  have assistant_messages := appendAssistant_messages session turn step
    round.source.assembly.result sourceEventSeqs sourcesNodup sourcesEarlier
  have assistant_next : session.nextSeq < assistant.nextSeq := by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append]
  have tool_messages := appendToolResults_messages assistant turn step
    session.nextSeq round.execution assistant_next
  change (appendToolResults assistant turn step session.nextSeq round.execution
      assistant_next).messages = _
  rw [tool_messages, assistant_messages]

/-! ## Executable wire-backed counter round -/

def counterRound :
    Except StreamToolRoundError
      (ValidatedStreamToolRound Cordis.Harness.counterConfig 2 counterBody) :=
  executeBodyTools Cordis.Harness.counterConfig 2 counterBody

def counterSummary : Bool :=
  match counterRound with
  | .error _ => false
  | .ok round =>
      round.execution.after == 5 &&
      round.execution.calls.length == 1 &&
      round.execution.executions.length == 1

def counterFinalSession : Option (Session.Session Session.noExtensions) :=
  match counterRound with
  | .error _ => none
  | .ok round =>
      some (appendRound (Session.Session.empty Session.noExtensions) 1 0 round []
        (by simp) (by simp))

def counterSessionSummary : Bool :=
  match counterFinalSession with
  | none => false
  | some session => session.messages.length == 2 && session.nextSeq == 2

end Cordis.DeepSeekStreamToolRound
