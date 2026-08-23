import Cordis.DeepSeekHarnessLocalSseApiErrorRetryConversation
import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekHarness
import Cordis.DeepSeekRichStream

/-!
# File-origin restored API-error retry conversation

This module composes the validated temporary-file archive boundary with the two-round local
HTTP/SSE API-error retry conversation.  The restored runner is indexed by the archive's final
session, and the second retry round is indexed by the first accepted append.  The result therefore
retains archive equality, both typed 429 envelopes, both request-build equations, and exact
session growth from the file-origin endpoint.

The temporary file is deleted by `IO.FS.withTempFile` after the fixture returns.  This proves a
filesystem-origin read and logical archive equality, not fsync, stable-media durability, crash
recovery, provider authenticity, backoff, idempotency, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceFileLocalSseApiErrorRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiErrorEnvelope
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseApiErrorRetryConversation
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekRichStream

abbrev Source : RequestSource := DeepSeekHarness.counterRequestSource

def key : ApiKey := { value := "fixture-key" }

def errorBody : String := DeepSeekApiErrorEnvelope.exampleBody

def successBody : String := DeepSeekRichStream.exampleTextStreamBody

structure FileApiErrorRetryConversationRun where
  restored : RestoredRunner
  conversation :
    ApiErrorRetryConversationResult Source restored.restored.runner

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : ApiErrorRetryConversationError)
deriving Repr

def runFixture : IO (Except EndToEndError FileApiErrorRetryConversationRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureFile with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runTwoRounds Source restored.restored.runner key errorBody successBody 64 with
      | .error error => pure (.error (.retry error))
      | .ok conversation => pure (.ok { restored, conversation })

theorem restored_session_eq_file_archive (run : FileApiErrorRetryConversationRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

theorem final_session_advance (run : FileApiErrorRetryConversationRun) :
    run.conversation.secondAfter.session.nextSeq =
      run.restored.restored.runner.session.nextSeq + 2 :=
  ApiErrorRetryConversationResult.session_advance_twice run.conversation

structure RequestProvenance (run : FileApiErrorRetryConversationRun) where
  first_archive_build :
    buildTypedStreamingRequestPlan
        (localBaseUrl run.conversation.first.accepted.port)
        run.conversation.first.accepted.prepared.key Source
        run.restored.read.validated.validated.final.session =
      .ok run.conversation.first.accepted.prepared.plan
  second_dependent_build :
    buildTypedStreamingRequestPlan
        (localBaseUrl run.conversation.second.accepted.port)
        run.conversation.second.accepted.prepared.key Source
        run.conversation.firstAfter.session =
      .ok run.conversation.second.accepted.prepared.plan
  first_body_eq_source :
    run.conversation.first.accepted.prepared.plan.request.body =
      Lean.Json.compress run.conversation.first.accepted.prepared.plan.source.toJson
  second_body_eq_source :
    run.conversation.second.accepted.prepared.plan.request.body =
      Lean.Json.compress run.conversation.second.accepted.prepared.plan.source.toJson

theorem requestProvenance (run : FileApiErrorRetryConversationRun) : RequestProvenance run :=
  {
    first_archive_build := by
      rw [← RestoredRunner.session_eq_read run.restored]
      exact run.conversation.first.accepted.prepared.build_eq
    second_dependent_build := run.conversation.second.accepted.prepared.build_eq
    first_body_eq_source := run.conversation.first.accepted.prepared.plan.body_eq
    second_body_eq_source := run.conversation.second.accepted.prepared.plan.body_eq
  }

structure Summary where
  storage : String
  initialNextSeq : Nat
  finalNextSeq : Nat
  firstRequests : Nat
  secondRequests : Nat
  firstValidRequests : Nat
  secondValidRequests : Nat
  firstStatus : Nat
  secondStatus : Nat
  requestBodiesDistinct : Bool
  firstServerExit : UInt32
  secondServerExit : UInt32
deriving BEq, DecidableEq, Repr

def summary (run : FileApiErrorRetryConversationRun) : Summary :=
  {
    storage := "temporary-file"
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.conversation.secondAfter.session.nextSeq
    firstRequests := run.conversation.first.accepted.requests
    secondRequests := run.conversation.second.accepted.requests
    firstValidRequests := run.conversation.first.accepted.validRequests
    secondValidRequests := run.conversation.second.accepted.validRequests
    firstStatus := run.conversation.first.firstStatus
    secondStatus := run.conversation.second.firstStatus
    requestBodiesDistinct :=
      run.conversation.first.accepted.prepared.plan.request !=
        run.conversation.second.accepted.prepared.plan.request
    firstServerExit := run.conversation.first.accepted.serverExit
    secondServerExit := run.conversation.second.accepted.serverExit
  }

def expectedSummary : Summary :=
  {
    storage := "temporary-file"
    initialNextSeq := 8
    finalNextSeq := 10
    firstRequests := 2
    secondRequests := 2
    firstValidRequests := 2
    secondValidRequests := 2
    firstStatus := 429
    secondStatus := 429
    requestBodiesDistinct := true
    firstServerExit := 0
    secondServerExit := 0
  }

theorem expectedSummary_endpoint :
    expectedSummary.finalNextSeq = expectedSummary.initialNextSeq + 2 := by
  rfl

def summaryMatches (value : Summary) : Bool :=
  value == expectedSummary

def runSummary : IO (Except EndToEndError Summary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPersistenceFileLocalSseApiErrorRetryConversation
