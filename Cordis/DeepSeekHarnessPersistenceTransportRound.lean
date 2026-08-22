import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekApiSession
import Cordis.DeepSeekHarnessTransportContract

/-!
# Persistence-backed, single-decoder conversation/tool round

This module composes a validated JSONL restore, a complete typed request plan,
one injected HTTP response, one `ValidatedResponse`, strict session admission,
and typed tool execution.  The same dependent response certificate is used for
the assistant append and the final tool-result endpoint; no second response
decode is hidden behind the high-level round.

The result is a bounded proof-carrying Harness slice.  `ReadCertificate` and
the injected transport are explicit inputs, so this module does not claim live
provider reachability, credential validity, durability/fsync, retry or
concurrency semantics, external side-effect correctness, or deployed
TypeScript equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceTransportRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekHarnessPersistence

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

/-! ## Retained round certificate -/

structure ConversationTransportToolRound
    {Model Capability : Type}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : ConversationRunner)
    (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    (body : String)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    where
  plan_build_eq :
    buildTypedCompleteRequestPlan baseUrl apiKey source runner.session = .ok plan
  response : HttpResponse
  body_eq : response.body = body
  validated : ValidatedResponse body
  accepted : AcceptedApiResponse body
  accepted_validated_eq : accepted.validated = validated
  accepted_eq : acceptValidated validated = .ok accepted
  assistantRunner : ConversationRunner
  assistant_append_eq :
    assistantRunner = ConversationRunner.appendAcceptedApi runner accepted
      sourceEventSeqs sourcesNodup sourcesEarlier
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq = runner.session.nextSeq
  executions : List (ExecutedTool cfg)
  finalModel : Model
  executions_eq :
    executeFunctionCalls cfg before
        accepted.validated.response.choices.head.message.toolCalls =
      .ok (finalModel, executions)
  finalRunner : ConversationRunner
  final_append_eq :
    finalRunner = ConversationRunner.appendToolResults assistantRunner runner.nextCall
      assistantSeq executions (by
        rw [assistant_append_eq]
        rw [ConversationRunner.appendAcceptedApi_nextSeq]
        rw [← assistantSeq_eq]
        exact Nat.lt_succ_self _)

namespace ConversationTransportToolRound

theorem plan_build
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    buildTypedCompleteRequestPlan baseUrl apiKey source runner.session = .ok plan :=
  round.plan_build_eq

theorem request_body_eq
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (_round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    plan.request.body = Lean.Json.compress plan.source.toJson :=
  plan.body_eq

theorem validated_eq
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.accepted.validated = round.validated :=
  round.accepted_validated_eq

theorem assistant_endpoint
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.assistantRunner = ConversationRunner.appendAcceptedApi runner round.accepted
      sourceEventSeqs sourcesNodup sourcesEarlier :=
  round.assistant_append_eq

theorem final_endpoint
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.finalRunner = ConversationRunner.appendToolResults round.assistantRunner
      runner.nextCall round.assistantSeq round.executions (by
        rw [round.assistant_append_eq]
        rw [ConversationRunner.appendAcceptedApi_nextSeq]
        rw [← round.assistantSeq_eq]
        exact Nat.lt_succ_self _) :=
  round.final_append_eq

theorem final_nextSeq
    {Model Capability : Type}
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : ConversationTransportToolRound baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.finalRunner.session.nextSeq =
      runner.session.nextSeq + 1 + round.executions.length := by
  rw [round.final_append_eq]
  change (DeepSeekHarness.appendExecutedToolResults round.assistantRunner.session
      round.assistantRunner.turn round.assistantRunner.step runner.nextCall
      round.assistantSeq round.executions _).nextSeq = _
  rw [DeepSeekHarness.appendExecutedToolResults_nextSeq]
  rw [round.assistant_append_eq]
  rw [ConversationRunner.appendAcceptedApi_nextSeq]

end ConversationTransportToolRound

/-! ## One-decoder transport execution -/

inductive RoundError where
  | request (error : RequestError)
  | transport (message : String)
  | httpStatus (status : Nat) (body : String)
  | response (error : ResponseError)
  | session (error : ApiSessionError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

def executeSource
    {Model Capability : Type}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun plan : TypedRequestPlan .complete =>
        Sigma fun body : String =>
          ConversationTransportToolRound baseUrl apiKey source runner plan
            (sourceEventSeqs := sourceEventSeqs)
            (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier)
            body cfg before)) := do
  match built : buildTypedCompleteRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← transport.send plan.request with
      | .error message => pure (.error (.transport message))
      | .ok response =>
          if successfulStatus response.status then
            match validatedEq : validateResponse response.body with
            | .error error => pure (.error (.response error))
            | .ok validated =>
                match acceptedEq : acceptValidated validated with
                | .error error => pure (.error (.session error))
                | .ok accepted =>
                    let assistantSeq := runner.session.nextSeq
                    let assistantRunner := ConversationRunner.appendAcceptedApi runner accepted
                      sourceEventSeqs sourcesNodup sourcesEarlier
                    have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                      rw [ConversationRunner.appendAcceptedApi_nextSeq]
                      exact Nat.lt_succ_self _
                    match executionEq : executeFunctionCalls cfg before
                        accepted.validated.response.choices.head.message.toolCalls with
                    | .error error => pure (.error (.tool error))
                    | .ok (finalModel, executions) =>
                        let finalRunner := ConversationRunner.appendToolResults assistantRunner
                          runner.nextCall assistantSeq executions assistantSeqEarlier
                        pure (.ok ⟨plan, ⟨response.body, {
                          plan_build_eq := built
                          response
                          body_eq := rfl
                          validated
                          accepted
                          accepted_validated_eq :=
                            DeepSeekHarnessTransportContract.acceptValidated_validated
                              acceptedEq
                          accepted_eq := acceptedEq
                          assistantRunner
                          assistant_append_eq := rfl
                          assistantSeq
                          assistantSeq_eq := rfl
                          executions
                          finalModel
                          executions_eq := executionEq
                          finalRunner
                          final_append_eq := rfl
                        }⟩⟩)
          else
            pure (.error (.httpStatus response.status response.body))

/-! ## Byte-backed restoration attachment -/

structure PersistedRound
    {Model Capability : Type}
    (restored : RestoredRunner)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : ConversationRunner)
    (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    (body : String)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    where
  round : ConversationTransportToolRound baseUrl apiKey source runner plan
    (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
    (sourcesEarlier := sourcesEarlier) body cfg before
  runner_eq : runner = restored.restored.runner
  restored_session_eq : restored.restored.runner.session =
    restored.read.validated.validated.final.session

theorem PersistedRound.read_session
    {Model Capability : Type}
    (restored : RestoredRunner)
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : PersistedRound restored baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    restored.restored.runner.session = restored.read.validated.validated.final.session :=
  round.restored_session_eq

theorem PersistedRound.plan_build_archive
    {Model Capability : Type}
    (restored : RestoredRunner)
    (baseUrl : String) (apiKey : ApiKey) (source : RequestSource)
    (runner : ConversationRunner) (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (cfg : GenericHarness.Config Model Capability) (before : Model)
    (round : PersistedRound restored baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    buildTypedCompleteRequestPlan baseUrl apiKey source
        restored.read.validated.validated.final.session = .ok plan := by
  rw [← RestoredRunner.session_eq_read restored]
  rw [← round.runner_eq]
  exact round.round.plan_build_eq

def executeRestored
    {Model Capability : Type}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (restored : RestoredRunner)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs,
      source < restored.restored.runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun plan : TypedRequestPlan .complete =>
        Sigma fun body : String =>
          PersistedRound restored baseUrl apiKey source restored.restored.runner plan
            (sourceEventSeqs := sourceEventSeqs)
            (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier)
            body cfg before)) := do
  match ← executeSource transport baseUrl apiKey source cfg before
      restored.restored.runner sourceEventSeqs sourcesNodup sourcesEarlier with
  | .error error => pure (.error error)
  | .ok ⟨plan, ⟨body, round⟩⟩ =>
      pure (.ok ⟨plan, ⟨body, {
        round := round
        runner_eq := rfl
        restored_session_eq := RestoredRunner.session_eq_read restored
      }⟩⟩)

end Cordis.DeepSeekHarnessPersistenceTransportRound
