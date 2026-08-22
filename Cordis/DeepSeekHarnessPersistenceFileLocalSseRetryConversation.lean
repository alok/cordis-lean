import Cordis.DeepSeekHarnessLocalSseRetryConversation
import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekHarness
import Cordis.DeepSeekRichStream

/-!
# File-origin restored retry conversation

This module composes the byte-backed persistence fixture with the real two-round local SSE
retry conversation.  The temporary file is written and read through `DurableIO.FileBackend`,
the resulting `ReadCertificate` remains attached to the restored runner, and the second retry
round is indexed by the first round's exact appended runner.  The executable witness therefore
connects archive provenance, request rebuilding, transient failure evidence, and session growth.

The temporary file is deleted by `IO.FS.withTempFile` after the fixture returns.  This proves a
filesystem-origin read and logical archive equality, not fsync, stable-media durability, crash
recovery, provider authenticity, backpressure, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceFileLocalSseRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSseRetryConversation
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekRichStream

abbrev Source : RequestSource := DeepSeekHarness.counterRequestSource

def key : ApiKey := { value := "fixture-key" }

def body : String := DeepSeekRichStream.exampleTextStreamBody

structure FileRetryConversationRun where
  restored : RestoredRunner
  conversation : RetryConversationResult Source restored.restored.runner

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : RetryConversationError)
deriving Repr

def runFixture : IO (Except EndToEndError FileRetryConversationRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureFile with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runTwoRounds Source restored.restored.runner key body 1 with
      | .error error => pure (.error (.retry error))
      | .ok conversation => pure (.ok { restored, conversation })

theorem restored_session_eq_file_archive (run : FileRetryConversationRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

theorem final_session_advance (run : FileRetryConversationRun) :
    run.conversation.second.after.session.nextSeq =
      run.restored.restored.runner.session.nextSeq + 2 :=
  RetryConversationResult.session_advance_twice run.conversation

structure Summary where
  storage : String
  initialNextSeq : Nat
  finalNextSeq : Nat
  firstRequests : Nat
  secondRequests : Nat
  firstFailures : Nat
  secondFailures : Nat
  requestBodiesDistinct : Bool
  firstCompleted : Bool
  secondCompleted : Bool
deriving BEq, DecidableEq, Repr

def summary (run : FileRetryConversationRun) : Summary :=
  {
    storage := "temporary-file"
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.conversation.second.after.session.nextSeq
    firstRequests := run.conversation.first.requests
    secondRequests := run.conversation.second.requests
    firstFailures := run.conversation.first.failures.length
    secondFailures := run.conversation.second.failures.length
    requestBodiesDistinct :=
      run.conversation.first.prepared.plan.request != run.conversation.second.prepared.plan.request
    firstCompleted := Example.completed run.conversation.first.response
    secondCompleted := Example.completed run.conversation.second.response
  }

def expectedSummary : Summary :=
  {
    storage := "temporary-file"
    initialNextSeq := 8
    finalNextSeq := 10
    firstRequests := 2
    secondRequests := 2
    firstFailures := 1
    secondFailures := 1
    requestBodiesDistinct := true
    firstCompleted := true
    secondCompleted := true
  }

theorem expectedSummary_complete : expectedSummary.firstCompleted = true := rfl

def summaryMatches (value : Summary) : Bool :=
  value == expectedSummary

def runSummary : IO (Except EndToEndError Summary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPersistenceFileLocalSseRetryConversation
