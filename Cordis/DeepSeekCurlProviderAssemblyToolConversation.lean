import Cordis.DeepSeekCurlProviderAssemblyToolRound

/-!
# Bounded process-backed dependent tool conversations

This module lifts the incremental process/tool round into the existing `ConversationRunner`.
Each iteration builds its request from the current runner, retains a dependent provider-round
witness indexed by the model before the round, appends assistant and tool-result messages with
fresh local call IDs, and either stops on a no-tool response or returns an explicit fuel stop.

The deterministic fixture intentionally returns the same tool call twice, so it exercises actual
runner continuation (`2 → 5 → 8`, four appended messages, and two allocated call IDs).
It remains a bounded local process model: network/authentication, blocked-read interruption,
backpressure,
reconnects, persistence, external effects, and deployed Harness equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlProviderAssemblyToolConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlProviderAssemblyToolRound
open Cordis.DeepSeekCurlProviderAssemblyIncremental
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekSessionRunner

inductive ConversationRoundError where
  | process (error : ProcessToolRoundError)
deriving DecidableEq, Repr

def appendAssistantAt
    (runner : ConversationRunner)
    (assembled : Assembled)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    ConversationRunner :=
  let view := toAssistantView assembled
  let assignment := sequentialAssignment runner.nextCall view
  let session := StreamSession.appendAssistant runner.session runner.turn runner.step view
    assignment sourceEventSeqs sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + view.rawToolCalls.length
    toolCallCount_eq_nextCall := by
      have messagesEq : session.messages = runner.session.messages ++
          [.assistant view.content (StreamSession.toSessionToolCalls view assignment)] := by
        simp [session, StreamSession.appendAssistant, Session.Session.appendSurface,
          Session.Session.append, Session.Session.messages_eq_surface,
          StreamSession.toAssistantPayload]
      simp only [messagesEq]
      rw [toolCallCount_append, runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendAssistantAt_messages
    (runner : ConversationRunner)
    (assembled : Assembled)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendAssistantAt runner assembled sourceEventSeqs sourcesNodup
      sourcesEarlier).session.messages =
      runner.session.messages ++
        [.assistant (toAssistantView assembled).content
          (StreamSession.toSessionToolCalls (toAssistantView assembled)
            (sequentialAssignment runner.nextCall (toAssistantView assembled)))] := by
  change (StreamSession.appendAssistant runner.session runner.turn runner.step
      (toAssistantView assembled)
      (sequentialAssignment runner.nextCall (toAssistantView assembled))
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  simp [StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface,
    StreamSession.toAssistantPayload]

theorem appendAssistantAt_nextSeq
    (runner : ConversationRunner)
    (assembled : Assembled)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendAssistantAt runner assembled sourceEventSeqs sourcesNodup
      sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  rfl

structure ConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  source : ProcessedToolRound cfg before body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq
  executions : List (ExecutedTool cfg)

def executeRoundWith
    {Model Capability : Type}
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ConversationRoundError
      (Sigma fun body : String => ConversationRoundResult cfg before body)) := do
  match ← executeWith maxReads config request cfg before with
  | .error error => pure (.error (.process error))
  | .ok ⟨body, source⟩ =>
      let assistantSeq := runner.session.nextSeq
      let assistantRunner := appendAssistantAt runner
        source.provider.certificate.result sourceEventSeqs sourcesNodup sourcesEarlier
      have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
        rw [appendAssistantAt_nextSeq]
        exact Nat.lt_succ_self _
      let finalRunner := ConversationRunner.appendToolResults assistantRunner runner.nextCall
        assistantSeq source.execution.executions assistantSeqEarlier
      pure (.ok ⟨body, {
        source
        assistantRunner
        runner := finalRunner
        finalModel := source.execution.after
        assistantSeq
        assistantSeq_eq := by
          change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
          exact appendAssistantAt_nextSeq runner source.provider.certificate.result
            sourceEventSeqs sourcesNodup sourcesEarlier
        executions := source.execution.executions
      }⟩)

theorem ConversationRoundResult.execution_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : ConversationRoundResult cfg before body) :
    executeAssembledTools cfg before round.source.provider.certificate.result =
      .ok round.source.execution :=
  round.source.execution_eq

abbrev ConversationWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String =>
    ConversationRoundResult cfg before body

inductive ConversationStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : ConversationWitness cfg)
      (noToolCalls : last.2.2.source.execution.calls.length = 0)
  | fuelExhausted

structure ConversationRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (ConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : ConversationStop cfg

def runAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (maxReads : Nat)
    (config : ProcessConfig)
    (requestFor : ConversationRunner → HttpRequest)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (ConversationWitness cfg)) :
    IO (Except ConversationRoundError (ConversationRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeRoundWith maxReads config (requestFor runner) cfg before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : ConversationWitness cfg := ⟨before, ⟨body, round⟩⟩
          let nextHistory := history ++ [witness]
          if noTools : round.source.execution.calls.length = 0 then
            pure (.ok {
              rounds := nextHistory
              runner := round.runner
              finalModel := round.finalModel
              stop := .completed witness noTools
            })
          else
            runAux fuel maxReads config requestFor sourceEventSeqs sourcesNodup sourcesEarlier
              round.finalModel round.runner nextHistory
termination_by fuel

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel maxReads : Nat)
    (config : ProcessConfig)
    (requestFor : ConversationRunner → HttpRequest)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except ConversationRoundError (ConversationRunResult cfg)) :=
  runAux fuel maxReads config requestFor sourceEventSeqs sourcesNodup sourcesEarlier before
    runner []

def counterProcess : ProcessConfig :=
  DeepSeekCurlProviderAssemblyToolRound.counterProcess

def counterRequestFor (_runner : ConversationRunner) : HttpRequest :=
  DeepSeekCurlProviderAssemblyToolRound.counterRequest

def counterRun : IO (Except ConversationRoundError
    (ConversationRunResult Cordis.Harness.counterConfig)) :=
  run 2 64 counterProcess counterRequestFor [] (by simp) (by simp)
    2 (ConversationRunner.empty 1)

def counterSummary : IO Bool := do
  match ← counterRun with
  | .error _ => pure false
  | .ok result =>
      pure (result.rounds.length == 2 &&
        result.finalModel == 8 &&
        result.runner.session.messages.length == 4 &&
        result.runner.session.nextSeq == 4 &&
        result.runner.nextCall == 2)

end Cordis.DeepSeekCurlProviderAssemblyToolConversation
