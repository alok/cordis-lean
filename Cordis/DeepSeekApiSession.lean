import Cordis.DeepSeekApi
import Cordis.DeepSeekSessionRunner

/-!
# Proof-carrying non-streaming DeepSeek response to session bridge

`DeepSeekApi` already separates transport/status/API failures from a successful dependent
response decode. This module performs the next local refinement: it admits only a singleton
assistant choice whose index is zero, whose finish reason is one of the locally supported
successful reasons, and whose payload contains visible content or at least one tool call.

The accepted response is projected into the same `RichStream.AssistantMessageView` shape used by
the streaming bridge. A runner append then allocates fresh local numeric IDs from its proved
tool-call count. Provider IDs, reasoning text, transport, persistence, external tool execution,
and whole-session equivalence remain explicit boundaries.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekApiSession

open Cordis
open Cordis.RichStream
open Cordis.DeepSeekApi
open Cordis.DeepSeekSessionRunner

inductive ApiSessionError where
  | response (error : DeepSeekApi.ResponseError)
  | extraChoices (count : Nat)
  | wrongChoiceIndex (index : Nat)
  | missingFinish
  | unsupportedFinish (reason : DeepSeekApi.FinishReason)
  | emptyAssistant
deriving DecidableEq, Repr

structure AcceptedApiResponse (body : String) where
  validated : DeepSeekApi.ValidatedResponse body
  index_zero : validated.response.choices.head.index = 0
  singleton : validated.response.choices.tail = []
  finish : DeepSeekApi.FinishReason
  finish_eq : validated.response.choices.head.finishReason = some finish
  content_or_tool :
    validated.response.choices.head.message.content.isSome ∨
      validated.response.choices.head.message.toolCalls ≠ []

private def choicePayloadPresent (choice : DeepSeekApi.Choice) : Prop :=
  choice.message.content.isSome ∨ choice.message.toolCalls ≠ []

def acceptValidated {body : String} (validated : DeepSeekApi.ValidatedResponse body) :
    Except ApiSessionError (AcceptedApiResponse body) :=
  if hindex : validated.response.choices.head.index = 0 then
    if htail : validated.response.choices.tail = [] then
      match hfinish : validated.response.choices.head.finishReason with
      | none => .error .missingFinish
      | some .stop =>
          if hpayload :
              (validated.response.choices.head.message.content.isSome ∨
                validated.response.choices.head.message.toolCalls ≠ []) then
            .ok {
              validated
              index_zero := hindex
              singleton := htail
              finish := .stop
              finish_eq := hfinish
              content_or_tool := hpayload
            }
          else
            .error .emptyAssistant
      | some .length =>
          if hpayload :
              (validated.response.choices.head.message.content.isSome ∨
                validated.response.choices.head.message.toolCalls ≠ []) then
            .ok {
              validated
              index_zero := hindex
              singleton := htail
              finish := .length
              finish_eq := hfinish
              content_or_tool := hpayload
            }
          else
            .error .emptyAssistant
      | some .toolCalls =>
          if hpayload :
              (validated.response.choices.head.message.content.isSome ∨
                validated.response.choices.head.message.toolCalls ≠ []) then
            .ok {
              validated
              index_zero := hindex
              singleton := htail
              finish := .toolCalls
              finish_eq := hfinish
              content_or_tool := hpayload
            }
          else
            .error .emptyAssistant
      | some .contentFilter => .error (.unsupportedFinish .contentFilter)
      | some .insufficientSystemResource =>
          .error (.unsupportedFinish .insufficientSystemResource)
    else
      .error (.extraChoices validated.response.choices.tail.length)
  else
    .error (.wrongChoiceIndex validated.response.choices.head.index)

def acceptResponse (body : String) :
    Except ApiSessionError (AcceptedApiResponse body) :=
  match _parsed : DeepSeekApi.validateResponse body with
  | .error error => .error (.response error)
  | .ok validated => acceptValidated validated

def view {body : String} (accepted : AcceptedApiResponse body) :
    RichStream.AssistantMessageView :=
  let message := accepted.validated.response.choices.head.message
  {
    content := message.content.getD ""
    rawToolCalls := message.toolCalls.map (fun call => {
      providerId := call.id
      name := call.name
      rawArguments := call.arguments
    })
  }

theorem view_rawToolCalls_length {body : String}
    (accepted : AcceptedApiResponse body) :
    (view accepted).rawToolCalls.length =
      accepted.validated.response.choices.head.message.toolCalls.length := by
  simp [view]

theorem view_content {body : String}
    (accepted : AcceptedApiResponse body) :
    (view accepted).content =
      accepted.validated.response.choices.head.message.content.getD "" := by
  rfl

namespace Runner

def appendApi
    (runner : DeepSeekSessionRunner.Runner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    DeepSeekSessionRunner.Runner :=
  let assistantView := view accepted
  let assignment := sequentialAssignment runner.nextCall assistantView
  let session := StreamSession.appendAssistant runner.session runner.turn runner.step
    assistantView assignment sourceEventSeqs sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + assistantView.rawToolCalls.length
    nextSeq_eq_step := by
      change runner.session.nextSeq + 1 = runner.step + 1
      rw [runner.nextSeq_eq_step]
    toolCallCount_eq_nextCall := by
      have messages_eq :
          session.messages = runner.session.messages ++ [.assistant assistantView.content
            (StreamSession.toSessionToolCalls assistantView assignment)] := by
        simp [session, StreamSession.appendAssistant, Session.Session.appendSurface,
          Session.Session.append, Session.Session.messages_eq_surface,
          StreamSession.toAssistantPayload]
      simp only [messages_eq]
      rw [toolCallCount_append]
      rw [runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendApi_session_messages
    (runner : DeepSeekSessionRunner.Runner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant (view accepted).content
        (StreamSession.toSessionToolCalls (view accepted)
          (sequentialAssignment runner.nextCall (view accepted)))] := by
  change (StreamSession.appendAssistant runner.session runner.turn runner.step
      (view accepted) (sequentialAssignment runner.nextCall (view accepted))
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  simp [StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface,
    StreamSession.toAssistantPayload]

theorem appendApi_nextSeq
    (runner : DeepSeekSessionRunner.Runner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
  rfl

theorem appendApi_nextCall
    (runner : DeepSeekSessionRunner.Runner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall +
        accepted.validated.response.choices.head.message.toolCalls.length := by
  change runner.nextCall + (view accepted).rawToolCalls.length = _
  rw [view_rawToolCalls_length]

def appendBody
    (runner : DeepSeekSessionRunner.Runner)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except ApiSessionError DeepSeekSessionRunner.Runner :=
  match acceptResponse body with
  | .error error => .error error
  | .ok accepted =>
      .ok (appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier)

end Runner

/-! ## Deterministic successful fixture -/

def acceptedExample :
    Except ApiSessionError (AcceptedApiResponse DeepSeekApi.exampleResponseBody) :=
  acceptResponse DeepSeekApi.exampleResponseBody

end Cordis.DeepSeekApiSession
