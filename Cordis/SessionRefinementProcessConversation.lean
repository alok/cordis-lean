import Cordis.SessionRefinementProcess
import Cordis.DeepSeekHarnessTransportRetryConversation

/-!
# Process-backed session events into a retry-aware Harness conversation

This is the next composition boundary after `SessionRefinementProcess`: the local subprocess
event prefix becomes the exact initial index of a `ConversationRunner`, and the existing bounded
retry-aware transport loop is run from that runner.  The dependent result stores both the process
cursor and the conversation trace, so a conversation cannot silently start from a different
session endpoint.  The transport remains deterministic and injected; this does not claim live
DeepSeek reachability, credentials, provider behavior, backoff, idempotency, or deployed runtime
equivalence.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinementProcessConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventPrefix
open Cordis.DeepSeekHarnessEventProcessPrefix
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekHarnessTransportRetry
open Cordis.DeepSeekHarnessTransportRetryConversation

abbrev FixturePolicy := DeepSeekHarnessTransportRetryConversation.Example.retryConversationPolicy
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier (runner : ConversationRunner) :
    ∀ source ∈ emptySourceEventSeqs, source < runner.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-- A conversation runner whose session is exactly the process cursor endpoint. -/
structure RestoredRunner where
  process : ProcessPrefixResult EntryPolicy.never
  runner : ConversationRunner
  session_eq : runner.session = process.cursor.final.session
  step_eq : runner.step = process.cursor.final.session.nextSeq

def restoreRunner (process : ProcessPrefixResult EntryPolicy.never) : RestoredRunner := {
  process
  runner := {
    session := process.cursor.final.session
    turn := 1
    step := process.cursor.final.session.nextSeq
    nextCall := toolCallCount process.cursor.final.session.messages
    toolCallCount_eq_nextCall := rfl
  }
  session_eq := rfl
  step_eq := rfl
}

theorem RestoredRunner.session_eq_cursor (restored : RestoredRunner) :
    restored.runner.session = restored.process.cursor.final.session :=
  restored.session_eq

theorem RestoredRunner.step_eq_cursor (restored : RestoredRunner) :
    restored.runner.step = restored.process.cursor.final.session.nextSeq :=
  restored.step_eq

inductive EndToEndError where
  | process (error : ProcessPrefixError)
  | conversation (error : RetryRoundError FixturePolicy)

structure ProcessConversationRun where
  restored : RestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  conversation : RetryTransportConversationRunResult FixturePolicy FixtureConfig
    FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.runner 0 finalRunner finalModel

/-- Read the canonical event process, then continue from its exact session endpoint. -/
def runFixture : IO (Except EndToEndError ProcessConversationRun) := do
  match ← SessionRefinementProcess.runCanonicalProcess with
  | .error error => pure (.error (.process error))
  | .ok process =>
      let restored := restoreRunner process
      let calls ← IO.mkRef 0
      match ← DeepSeekHarnessTransportRetryConversation.runTransport
          (policy := FixturePolicy) 2
          (DeepSeekHarnessTransportRetryConversation.Example.retryConversationTransport calls)
          FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
          emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
          0 restored.runner with
      | .error error => pure (.error (.conversation error))
      | .ok ⟨finalRunner, ⟨finalModel, conversation⟩⟩ =>
          pure (.ok { restored, finalRunner, finalModel, conversation })

def firstRetryFailures
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
  RetryTransportTrace FixturePolicy FixtureConfig FixtureBaseUrl FixtureApiKey FixtureSource
      emptySourceEventSeqs emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
      runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.failures.length

structure ExecutableSummary where
  eventCount : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  conversationRounds : Nat
  retryFailures : Nat
  finalModel : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def summary (run : ProcessConversationRun) : ExecutableSummary := {
  eventCount := run.restored.process.cursor.entries.length
  initialNextSeq := run.restored.runner.session.nextSeq
  finalNextSeq := run.finalRunner.session.nextSeq
  conversationRounds := RetryTransportTrace.length run.conversation.trace
  retryFailures := firstRetryFailures run.conversation.trace
  finalModel := run.finalModel
  completed := run.conversation.stop.isCompleted
}

def expectedSummary : ExecutableSummary := {
  eventCount := 4
  initialNextSeq := 4
  finalNextSeq := 7
  conversationRounds := 2
  retryFailures := 1
  finalModel := 0
  completed := true
}

def summaryMatches (value : ExecutableSummary) : Bool :=
  value.eventCount = expectedSummary.eventCount &&
    value.initialNextSeq = expectedSummary.initialNextSeq &&
    value.finalNextSeq = expectedSummary.finalNextSeq &&
    value.conversationRounds = expectedSummary.conversationRounds &&
    value.retryFailures = expectedSummary.retryFailures &&
    value.finalModel = expectedSummary.finalModel &&
    value.completed = expectedSummary.completed

theorem restored_session_eq_process (run : ProcessConversationRun) :
    run.restored.runner.session = run.restored.process.cursor.final.session :=
  run.restored.session_eq

theorem restored_projection_eq_process (run : ProcessConversationRun) :
    run.restored.process.cursor.sequence.protocolTrace.erase =
      run.restored.process.cursor.sequence.runtimeEvents :=
  SessionRefinementProcess.processResult_projection
    (result := run.restored.process)

end Cordis.SessionRefinementProcessConversation
