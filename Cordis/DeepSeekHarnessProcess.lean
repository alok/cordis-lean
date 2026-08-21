import Cordis.DeepSeekCurlSession
import Cordis.DeepSeekHarness

/-!
# Request-provenance process rounds

`DeepSeekCurlSession` already validates a complete process-backed SSE body and appends its
finished view to the small `DeepSeekSessionRunner.Runner`.  Its low-level entry point accepts an
`HttpRequest`, however, so the request source and the proof that the request was built from the
runner session can otherwise disappear at the process boundary.

This module keeps that provenance indexed.  A `PreparedRequest` retains the typed Harness
`RequestSource`, the exact `RequestPlan`, and the successful `buildRequestPlan` equation.  A
`ProcessRound` then retains the process/wire/semantic response and the exact append endpoint.
The convenience executor first constructs the prepared request and only then launches the
process.  Request-construction failures therefore remain distinct from process, status, stream,
and terminal-response failures.

The adapter is deliberately complete-body and targets the local `DeepSeekSessionRunner.Runner`.
It does not claim provider schema equivalence, credential validity, incremental delivery,
cancellation of blocked reads, persistence, external tool execution, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessProcess

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner

/-! ## Prepared request provenance -/

/-- A request plan tied to the exact Harness source and runner session that produced it. -/
structure PreparedRequest
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : Runner) where
  plan : RequestPlan
  build_eq : buildRequestPlan baseUrl apiKey source runner.session = .ok plan

namespace PreparedRequest

theorem build_exact
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner) :
    buildRequestPlan baseUrl apiKey source runner.session = .ok prepared.plan :=
  prepared.build_eq

theorem body_eq_source
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRequest

/-- Build a request while retaining the dependent success equation. -/
def prepareRequest
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : Runner) :
    Except RequestError (PreparedRequest baseUrl apiKey source runner) :=
  match built : buildRequestPlan baseUrl apiKey source runner.session with
  | .error error => .error error
  | .ok plan => .ok { plan, build_eq := built }

/-! ## Process-round certificate -/

/-- A successful process response and its exact append endpoint. -/
structure ProcessRound
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq)
    (body : String) where
  processed : ProcessedResponse body
  after : Runner
  append_eq : after = appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier

namespace ProcessRound

theorem append_endpoint
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : ProcessRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after = appendProcessed runner round.processed sourceEventSeqs sourcesNodup
      sourcesEarlier :=
  round.append_eq

theorem nextSeq
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : ProcessRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [round.append_eq]
  exact appendProcessed_nextSeq runner round.processed sourceEventSeqs sourcesNodup sourcesEarlier

theorem nextCall
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : ProcessRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after.nextCall = runner.nextCall +
      round.processed.finished.finished.view.rawToolCalls.length := by
  rw [round.append_eq]
  exact appendProcessed_nextCall runner round.processed sourceEventSeqs sourcesNodup sourcesEarlier

end ProcessRound

/-! ## Typed process execution -/

inductive ExecutionError where
  | request (error : RequestError)
  | client (error : SessionClientError)
deriving DecidableEq, Repr

def executePrepared
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (config : ProcessConfig)
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SessionClientError
      (Sigma fun body : String =>
        ProcessRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  match ← executeWith finish config prepared.plan.request with
  | .error error => pure (.error error)
  | .ok ⟨body, processed⟩ =>
      pure (.ok ⟨body, {
        processed
        after := appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier
        append_eq := rfl
      }⟩)

def executePreparedText
    (config : ProcessConfig)
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
  executePrepared finishText config prepared sourceEventSeqs sourcesNodup sourcesEarlier

/-- Prepare a typed source and execute it, retaining request or process failure separately. -/
def executeSource
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ExecutionError
      (Sigma fun prepared : PreparedRequest baseUrl apiKey source runner =>
        Sigma fun body : String =>
          ProcessRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  match prepareRequest baseUrl apiKey source runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePrepared finish config prepared sourceEventSeqs sourcesNodup
          sourcesEarlier with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, round⟩ => pure (.ok ⟨prepared, ⟨body, round⟩⟩)

def executeSourceText
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
  executeSource finishText config baseUrl apiKey source runner sourceEventSeqs
    sourcesNodup sourcesEarlier

/-! ## Executable source/provenance fixtures -/

def fixtureSource : RequestSource where
  model := "fixture-model"
  system := some "fixture-system"

def fixturePrepared :
    Except RequestError
      (PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
        fixtureSource (Runner.empty 1)) :=
  prepareRequest "https://fixture.invalid" { value := "fixture-key" }
    fixtureSource (Runner.empty 1)

def fixtureText : IO (Except ExecutionError
    (Sigma fun prepared : PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
      fixtureSource (Runner.empty 1) =>
      Sigma fun body : String => ProcessRound prepared [] (by simp) (by simp) body)) :=
  executeSourceText DeepSeekCurlSession.fixtureTextProcess "https://fixture.invalid"
    { value := "fixture-key" } fixtureSource (Runner.empty 1) [] (by simp) (by simp)

end Cordis.DeepSeekHarnessProcess
