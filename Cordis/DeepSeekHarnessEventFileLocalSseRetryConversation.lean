import Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
import Cordis.DeepSeekHarnessLocalSseRetryConversation
import Cordis.DeepSeekHarness
import Cordis.DeepSeekRichStream

/-!
# Current-event file restore into loopback SSE retry conversation

This module composes the supported current-Harness event archive with the real two-round
loopback HTTP/SSE retry conversation.  The event JSONL fixture is written to a temporary file,
read back through the byte/UTF-8/JSONL certificate, and only then used as the dependent initial
`ConversationRunner`.  The first and second loopback rounds retain their own prepared request
plans; the second plan is indexed by the exact runner produced by the first accepted response.

The result therefore connects current-event restoration, request reconstruction, transient HTTP
retry evidence, and dependent session growth in one executable witness.  It does not claim that
the loopback server is a provider, that the temporary file is durable, that the process adapter
authenticates a live deployment, or that blocked reads, cleanup, backpressure, reconnect policy,
or deployed Harness equivalence have been proved.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventFileLocalSseRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseRetryConversation
open Cordis.DeepSeekRichStream

abbrev Source : RequestSource := DeepSeekHarness.counterRequestSource

def key : ApiKey := { value := "fixture-key" }

def body : String := DeepSeekRichStream.exampleTextStreamBody

abbrev FileRestored :=
  DeepSeekHarnessEventFileStreamRetryCancellation.FileRestored

structure EventFileRetryConversationRun where
  file : FileRestored
  conversation : RetryConversationResult Source
    file.restored.restored.restored.runner

inductive EndToEndError where
  | file (error : FileReadError)
  | retry (error : RetryConversationError)
deriving Repr

def runFixture : IO (Except EndToEndError EventFileRetryConversationRun) := do
  match ← DeepSeekHarnessEventFileStreamRetryCancellation.restoreFile with
  | .error error => pure (.error (.file error))
  | .ok file =>
      match ← runTwoRounds Source file.restored.restored.restored.runner key body 1 with
      | .error error => pure (.error (.retry error))
      | .ok conversation => pure (.ok { file, conversation })

theorem file_bytes_eq_source (run : EventFileRetryConversationRun) :
    run.file.bytes = DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes :=
  run.file.bytes_eq_source

theorem restored_session_eq_event_archive (run : EventFileRetryConversationRun) :
    run.file.restored.restored.restored.runner.session =
      run.file.restored.restored.validated.validated.final.session :=
  RestoredTextRunner.session_eq run.file.restored.restored

structure RequestProvenance (run : EventFileRetryConversationRun) where
  first_archive_build :
    buildTypedStreamingRequestPlan (localBaseUrl run.conversation.first.port)
        run.conversation.first.prepared.key Source
        run.file.restored.restored.validated.validated.final.session =
      .ok run.conversation.first.prepared.plan
  second_dependent_build :
    buildTypedStreamingRequestPlan (localBaseUrl run.conversation.second.port)
        run.conversation.second.prepared.key Source
        run.conversation.first.after.session =
      .ok run.conversation.second.prepared.plan
  first_body_eq_source :
    run.conversation.first.prepared.plan.request.body =
      Lean.Json.compress run.conversation.first.prepared.plan.source.toJson
  second_body_eq_source :
    run.conversation.second.prepared.plan.request.body =
      Lean.Json.compress run.conversation.second.prepared.plan.source.toJson

theorem requestProvenance (run : EventFileRetryConversationRun) :
    RequestProvenance run :=
  {
    first_archive_build := by
      rw [← restored_session_eq_event_archive run]
      exact run.conversation.first.prepared.build_eq
    second_dependent_build := run.conversation.second.prepared.build_eq
    first_body_eq_source := run.conversation.first.prepared.plan.body_eq
    second_body_eq_source := run.conversation.second.prepared.plan.body_eq
  }

theorem final_session_advance (run : EventFileRetryConversationRun) :
    run.conversation.second.after.session.nextSeq =
      run.file.restored.restored.restored.runner.session.nextSeq + 2 :=
  RetryConversationResult.session_advance_twice run.conversation

structure Summary where
  storage : String
  sourceBytes : Nat
  readBytes : Nat
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

def summary (run : EventFileRetryConversationRun) : Summary :=
  {
    storage := "temporary-file-current-event"
    sourceBytes := DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes.size
    readBytes := run.file.bytes.size
    initialNextSeq := run.file.restored.restored.restored.runner.session.nextSeq
    finalNextSeq := run.conversation.second.after.session.nextSeq
    firstRequests := run.conversation.first.requests
    secondRequests := run.conversation.second.requests
    firstFailures := run.conversation.first.failures.length
    secondFailures := run.conversation.second.failures.length
    requestBodiesDistinct :=
      run.conversation.first.prepared.plan.request.body !=
        run.conversation.second.prepared.plan.request.body
    firstCompleted := Example.completed run.conversation.first.response
    secondCompleted := Example.completed run.conversation.second.response
  }

def expectedSummary : Summary :=
  {
    storage := "temporary-file-current-event"
    sourceBytes := DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes.size
    readBytes := DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes.size
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

def summaryMatches (value : Summary) : Bool := value == expectedSummary

def runSummary : IO (Except EndToEndError Summary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessEventFileLocalSseRetryConversation
