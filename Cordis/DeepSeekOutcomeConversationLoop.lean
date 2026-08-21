import Cordis.DeepSeekOutcomeConversation

/-!
# Fuel-bounded terminal-outcome conversation loop

`DeepSeekOutcomeConversation` handles one complete terminal outcome. This module adds the
caller-fueled continuation that a harness needs after a tool round: each successful outcome is
executed and appended, tool-bearing rounds continue with the returned model/session, and a
successful outcome with no tool calls is a typed completion. Provider failures remain terminal
typed values, while an empty body script or exhausted fuel is distinct from a transport error.

The script runner is intentionally pure over already-observed complete bodies. It proves the
conversation/model transitions after validation and dependent tool execution; process reads,
request rebuilding, retry, persistence, cancellation, and provider/deployment equivalence remain
the surrounding adapter's responsibilities.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekOutcomeConversationLoop

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekOutcomeConversation
open Cordis.DeepSeekStreamFailure
open Cordis.DeepSeekTerminalOutcome
open Cordis.DeepSeekHarness

abbrev OutcomeWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String => ExecutedRound cfg before body

inductive OutcomeRunError where
  | terminal (error : TerminalOutcomeError)
  | execution (error : ExecutionError)
deriving DecidableEq, Repr

inductive OutcomeRunStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : OutcomeWitness cfg)
      (noCalls : last.2.2.executions.length = 0)
  | providerFailure
      {body : String}
      (validated : ValidatedFailureStream body)
      (runner : ConversationRunner)
  | fuelExhausted

structure OutcomeRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (OutcomeWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : OutcomeRunStop cfg

def runOutcomeBodiesAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (bodies : List String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (OutcomeWitness cfg)) :
    Except OutcomeRunError (OutcomeRunResult cfg) :=
  match fuel with
  | 0 =>
      .ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      }
  | fuel + 1 =>
      match bodies with
      | [] =>
          .ok {
            rounds := history
            runner
            finalModel := before
            stop := .fuelExhausted
          }
      | body :: rest =>
          match validateTerminalOutcome body with
          | .error error => .error (.terminal error)
          | .ok outcome =>
              match executeOutcomeWithTools cfg before runner outcome sourceEventSeqs
                  sourcesNodup (sourcesEarlier runner) with
              | .error error => .error (.execution error)
              | .ok (.providerFailure validated failureRunner) =>
                  .ok {
                    rounds := history
                    runner := failureRunner
                    finalModel := before
                    stop := .providerFailure validated failureRunner
                  }
              | .ok (.assistant round) =>
                  let witness : OutcomeWitness cfg := ⟨before, ⟨body, round⟩⟩
                  let nextHistory := history ++ [witness]
                  if noCalls : round.executions.length = 0 then
                    .ok {
                      rounds := nextHistory
                      runner := round.runner
                      finalModel := round.finalModel
                      stop := .completed witness noCalls
                    }
                  else
                    runOutcomeBodiesAux fuel rest sourceEventSeqs sourcesNodup sourcesEarlier
                      round.finalModel round.runner nextHistory

def runOutcomeBodies
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (bodies : List String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    Except OutcomeRunError (OutcomeRunResult cfg) :=
  runOutcomeBodiesAux fuel bodies sourceEventSeqs sourcesNodup sourcesEarlier before runner []

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    (runner : ConversationRunner) :
    ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

def exampleOutcomeBodies : List String := [
  DeepSeekOutcomeConversation.counterToolStreamBody,
  DeepSeekRichStream.exampleTextStreamBody
]

def exampleRun : Except OutcomeRunError
    (OutcomeRunResult Cordis.Harness.counterConfig) :=
  runOutcomeBodies 3 exampleOutcomeBodies [] emptySourcesNodup
    (fun current => emptySourcesEarlier current) 0
    (ConversationRunner.empty 1)

theorem runOutcomeBodies_empty_fuel
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (bodies : List String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    runOutcomeBodies (cfg := cfg) 0 bodies sourceEventSeqs sourcesNodup
        sourcesEarlier before runner =
      .ok {
        rounds := []
        runner
        finalModel := before
        stop := .fuelExhausted
      } := by
  rfl

theorem runOutcomeBodies_empty_script
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    runOutcomeBodies (cfg := cfg) fuel [] sourceEventSeqs sourcesNodup
        sourcesEarlier before runner =
      .ok {
        rounds := []
        runner
        finalModel := before
        stop := .fuelExhausted
      } := by
  cases fuel <;> rfl

end Cordis.DeepSeekOutcomeConversationLoop
