import Cordis.DeepSeekCurlIncremental
import Cordis.DeepSeekOutcomeSession

/-!
# Incremental process responses into typed terminal session outcomes

`DeepSeekCurlIncremental` exposes the line observations and the reconstructed,
strictly validated SSE body. This module composes that boundary with
`DeepSeekTerminalOutcome` and the local session runner: a provider failure is
retained as a typed terminal value without changing the runner, while a
successful text/tool/mixed/multi projection is finished and appended.

The result is intentionally a process-backed, line-oriented adapter. It does
not claim byte-level framing, backpressure, cancellation, reconnects,
credential or executable authenticity, provider-complete assembly, or
equivalence to a deployed DeepSeek Harness transport.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlIncrementalOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekOutcomeSession
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekTerminalOutcome

inductive IncrementalOutcomeError where
  | incremental (error : IncrementalError)
  | outcome (error : TerminalOutcomeError)
  | dispatch (error : DispatchError)
deriving DecidableEq, Repr

structure ProcessedOutcome (body : String) where
  response : IncrementalResponse body
  outcome : TerminalOutcome body
  outcome_exact : validateTerminalOutcome body = .ok outcome

def executeOutcome
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (onLine : Nat → String → IO Unit) :
    IO (Except IncrementalOutcomeError
      (Sigma fun body : String => ProcessedOutcome body)) := do
  match ← executeSseIncremental maxReads config request onLine with
  | .error error => pure (.error (.incremental error))
  | .ok ⟨body, response⟩ =>
      match h : validateTerminalOutcome body with
      | .error error => pure (.error (.outcome error))
      | .ok outcome => pure (.ok ⟨body, {
          response
          outcome
          outcome_exact := h
        }⟩)

def executeAndDispatchOutcome
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq)
    (onLine : Nat → String → IO Unit) :
    IO (Except IncrementalOutcomeError
      (Sigma fun body : String => DispatchResult body)) := do
  match ← executeOutcome maxReads config request onLine with
  | .error error => pure (.error error)
  | .ok ⟨body, processed⟩ =>
      match dispatchOutcome runner processed.outcome sourceEventSeqs
          sourcesNodup sourcesEarlier with
      | .error error => pure (.error (.dispatch error))
      | .ok result => pure (.ok ⟨body, result⟩)

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by
  simp

private theorem emptySourcesEarlier
    (runner : Runner) : ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

def fixtureFailure : IO (Except IncrementalOutcomeError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome 64
    (DeepSeekCurlIncremental.fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request (fun _ _ => pure ())

def fixtureText : IO (Except IncrementalOutcomeError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome 64
    (DeepSeekCurlIncremental.fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (fun _ _ => pure ())

def fixtureFailureDispatch : IO (Except IncrementalOutcomeError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome 64
    (DeepSeekCurlIncremental.fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1)) (fun _ _ => pure ())

def fixtureTextDispatch : IO (Except IncrementalOutcomeError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome 64
    (DeepSeekCurlIncremental.fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1)) (fun _ _ => pure ())

theorem outcome_exact_failure
    {body : String} {processed : ProcessedOutcome body}
    {validated : DeepSeekStreamFailure.ValidatedFailureStream body}
    (h : processed.outcome = .failure validated) :
    validateTerminalOutcome body = .ok (.failure validated) := by
  simpa [h] using processed.outcome_exact

theorem outcome_exact_text
    {body : String} {processed : ProcessedOutcome body}
    {validated : DeepSeekRichStream.ValidatedTextStream body}
    (h : processed.outcome = .text validated) :
    validateTerminalOutcome body = .ok (.text validated) := by
  simpa [h] using processed.outcome_exact

end Cordis.DeepSeekCurlIncrementalOutcome
