import Cordis.DeepSeekHarnessLocalSseRetry
import Cordis.DeepSeekHarness
import Cordis.DeepSeekRichStream

/-!
# Loopback retry-aware request/session conversation

This module lifts the one-round local SSE retry witness into a dependent conversation.  Each
round starts a bounded loopback server, validates both typed attempts, returns one transient HTTP
503 followed by a real curl/SSE success, and appends only the accepted terminal response.  The
second round is indexed by the first round's exact `ConversationRunner`, so its request body is
rebuilt from the appended session rather than reused by convention.

The fixture is finite and local.  It does not claim provider backoff, tool idempotency, arbitrary
retry policy, blocked-read cancellation, byte-level backpressure, credential/TLS authenticity,
persistence, external effects, or deployed Harness retry/conversation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSseRetry
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

structure RetryConversationResult
    (source : RequestSource)
    (runner : ConversationRunner) where
  first : LocalSseRetryResult source runner
  second : LocalSseRetryResult source first.after

namespace RetryConversationResult

theorem first_attempts
    {source : RequestSource} {runner : ConversationRunner}
    (result : RetryConversationResult source runner) :
    result.first.attempts = result.first.failures.length + 1 :=
  result.first.attempts_eq

theorem second_attempts
    {source : RequestSource} {runner : ConversationRunner}
    (result : RetryConversationResult source runner) :
    result.second.attempts = result.second.failures.length + 1 :=
  result.second.attempts_eq

theorem final_endpoint
    {source : RequestSource} {runner : ConversationRunner}
    (result : RetryConversationResult source runner) :
    result.second.after =
      ConversationRunner.appendFinished result.first.after result.second.finished []
        (by simp) (by simp) :=
  result.second.append_eq

theorem session_advance_twice
    {source : RequestSource} {runner : ConversationRunner}
    (result : RetryConversationResult source runner) :
    result.second.after.session.nextSeq = runner.session.nextSeq + 2 := by
  rw [result.second.append_eq]
  rw [ConversationRunner.appendFinished_nextSeq]
  rw [result.first.append_eq]
  rw [ConversationRunner.appendFinished_nextSeq]

end RetryConversationResult

inductive RetryConversationError where
  | first (error : LocalSseRetryError)
  | second (error : LocalSseRetryError)
deriving DecidableEq, Repr

def runTwoRounds
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (body : String)
    (maxRetries : Nat := 1) :
    IO (Except RetryConversationError (RetryConversationResult source runner)) := do
  match ← DeepSeekHarnessLocalSseRetry.runWithRetry source runner key body maxRetries with
  | .error error => pure (.error (.first error))
  | .ok first =>
      match ← DeepSeekHarnessLocalSseRetry.runWithRetry source first.after key body
          maxRetries with
      | .error error => pure (.error (.second error))
      | .ok second => pure (.ok { first, second })

namespace Example

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def source : RequestSource := DeepSeekHarness.counterRequestSource

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except RetryConversationError (RetryConversationResult source runner)) :=
  runTwoRounds source runner { value := "fixture-key" } body 1

def completed {body : String} (response : IncrementalResponse body) : Bool :=
  response.wire.frames.any (fun frame => match frame with
    | .done => true
    | .data _ => false)

structure Summary where
  firstRequests : Nat
  secondRequests : Nat
  firstValidRequests : Nat
  secondValidRequests : Nat
  firstFailures : Nat
  secondFailures : Nat
  requestBodiesDistinct : Bool
  finalNextSeq : Nat
  firstCompleted : Bool
  secondCompleted : Bool
deriving BEq, DecidableEq, Repr

def summarize (result : RetryConversationResult source runner) : Summary :=
  {
    firstRequests := result.first.requests
    secondRequests := result.second.requests
    firstValidRequests := result.first.validRequests
    secondValidRequests := result.second.validRequests
    firstFailures := result.first.failures.length
    secondFailures := result.second.failures.length
    requestBodiesDistinct :=
      result.first.prepared.plan.request.body != result.second.prepared.plan.request.body
    finalNextSeq := result.second.after.session.nextSeq
    firstCompleted := completed result.first.response
    secondCompleted := completed result.second.response
  }

def expectedSummary : Summary :=
  {
    firstRequests := 2
    secondRequests := 2
    firstValidRequests := 2
    secondValidRequests := 2
    firstFailures := 1
    secondFailures := 1
    requestBodiesDistinct := true
    finalNextSeq := 3
    firstCompleted := true
    secondCompleted := true
  }

theorem expectedSummary_complete : expectedSummary.firstCompleted = true := rfl

def summaryMatches (summary : Summary) : Bool :=
  summary == expectedSummary

def executableSummary : IO Bool := do
  match ← run with
  | .error _ => pure false
  | .ok result => pure (summaryMatches (summarize result))

end Example

end Cordis.DeepSeekHarnessLocalSseRetryConversation
