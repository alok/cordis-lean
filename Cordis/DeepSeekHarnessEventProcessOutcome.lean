import Cordis.DeepSeekHarnessEventText
import Cordis.DeepSeekHarnessProcessOutcome

/-!
# Current-Harness event refinement to a process-backed outcome round

`DeepSeekHarnessEventText` restores a supported current-Harness JSONL prefix into a
`ConversationRunner`, while `DeepSeekHarnessProcessOutcome` executes a complete streaming
process response from a `RequestSource`.  This module is the missing composition boundary:
the restored event-log certificate remains attached to the prepared request and to the final
rich/tool endpoint.

The request source is deliberately caller-supplied.  The supported event refinement retains
the upstream request-header witness, but the local request builder also contains policy fields
whose provider/deployment meaning is not recoverable from the accepted subset.  No theorem here
turns a restored event log into authenticated provider configuration.  Likewise, process,
credential, schema, persistence, cancellation, and deployed-Harness equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventProcessOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessProcessOutcome
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekOutcomeConversation
open Cordis.DeepSeekSessionRunner
open Cordis.SessionEventArchive
open Cordis.SessionRefinement

/-! ## Attached successful round -/

/-- A process-backed outcome round whose source runner is a refined event-log endpoint. -/
structure EventProcessRound
    {sourceText : String}
    (restored : RestoredTextRunner sourceText)
    {baseUrl : String}
    {apiKey : ApiKey}
    (source : RequestSource)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq)
    (prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner)
    (body : String) where
  round : ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup sourcesEarlier body
  restored_session_eq :
    restored.restored.runner.session = restored.validated.validated.final.session
  archive_raw_eq :
    restored.restored.log.archive.events.map ArchivedEvent.raw =
      restored.validated.parsed.lines

namespace EventProcessRound

theorem process_exact
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    (body : String)
    {prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner}
    (round : EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier prepared body) :
    executeOutcomeWithTools cfg before restored.restored.runner round.round.processed.outcome
        sourceEventSeqs sourcesNodup sourcesEarlier = .ok round.round.result :=
  round.round.result_exact

theorem endpoint_exact
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    (body : String)
    {prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner}
    (round : EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier prepared body) :
    round.round.after = executionEndpoint round.round.result :=
  round.round.endpoint_exact

theorem request_build_eq_restored_session
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    (body : String)
    {prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner}
    (round : EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier prepared body) :
    buildTypedStreamingRequestPlan baseUrl apiKey source
        restored.validated.validated.final.session = .ok prepared.plan := by
  rw [← round.restored_session_eq]
  exact prepared.build_eq

theorem archive_raw_eq_source
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    (body : String)
    {prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner}
    (round : EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier prepared body) :
    restored.restored.log.archive.events.map ArchivedEvent.raw =
      restored.validated.parsed.lines :=
  round.archive_raw_eq

theorem source_projection_exact
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    (body : String)
    {prepared : PreparedStreamingRequest baseUrl apiKey source restored.restored.runner}
    (_round : EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier prepared body) :
    Session.protocolProjection restored.validated.validated.final.session.events =
      restored.validated.validated.sequence.protocolTrace.erase :=
  ValidatedJsonLog.projection_exact restored.validated.validated

end EventProcessRound

/-! ## Text and byte entry points -/

/-- Prepare and execute a restored text event log through the rich outcome process seam. -/
def executeRestoredOutcome
    (config : ProcessConfig)
    {sourceText : String}
    (restored : RestoredTextRunner sourceText)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq) :
    IO (Except DeepSeekHarnessProcessOutcome.RoundError
      (Sigma fun prepared : PreparedStreamingRequest baseUrl apiKey source
          restored.restored.runner =>
        Sigma fun body : String =>
          EventProcessRound restored source cfg before sourceEventSeqs sourcesNodup
            sourcesEarlier prepared body)) := do
  match prepareStreamingRequest baseUrl apiKey source restored.restored.runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePreparedOutcome config cfg before prepared sourceEventSeqs sourcesNodup
          sourcesEarlier with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          pure (.ok ⟨prepared, ⟨body, {
            round
            restored_session_eq := restored.session_eq
            archive_raw_eq := restored.archive_raw_eq_lines
          }⟩⟩)

/-- A byte restoration retains its UTF-8 proof while the text certificate runs the round. -/
def executeRestoredBytesOutcome
    (config : ProcessConfig)
    {bytes : ByteArray}
    (restored : RestoredBytesRunner bytes)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.restored.runner.session.nextSeq) :
    IO (Except DeepSeekHarnessProcessOutcome.RoundError
      (Sigma fun prepared : PreparedStreamingRequest baseUrl apiKey source
          restored.restored.restored.runner =>
        Sigma fun body : String =>
          EventProcessRound restored.restored source cfg before sourceEventSeqs sourcesNodup
            sourcesEarlier prepared body)) :=
  executeRestoredOutcome config restored.restored baseUrl apiKey source cfg before sourceEventSeqs
    sourcesNodup sourcesEarlier

/-! ## Deterministic evidence -/

namespace Example

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    {sourceText : String} (restored : RestoredTextRunner sourceText) :
    ∀ eventSeq ∈ ([] : List Nat),
      eventSeq < restored.restored.runner.session.nextSeq := by
  simp

def restoredText : Except TextArchiveError
    (RestoredTextRunner DeepSeekHarnessEventText.toolTextSource) :=
  DeepSeekHarnessEventText.toolTextRestored

def restoredBytes : Except TextArchiveError
    (RestoredBytesRunner DeepSeekHarnessEventText.toolTextSource.toUTF8) :=
  DeepSeekHarnessEventText.toolBytesRestored

def source : RequestSource where
  model := "fixture-model"
  system := some "Execute only certified local tools."

def text : IO (Except DeepSeekHarnessProcessOutcome.RoundError String) := do
  match restoredText with
  | .error _ => pure (.error (.request .emptyMessages))
  | .ok restored =>
      match ← executeRestoredOutcome DeepSeekHarnessProcessOutcome.Example.textProcess restored
          "https://fixture.invalid" { value := "fixture-key" } source
          Cordis.Harness.counterConfig 0 [] emptySourcesNodup
          (emptySourcesEarlier restored) with
      | .error error => pure (.error error)
      | .ok ⟨_, ⟨body, _⟩⟩ => pure (.ok body)

def bytes : IO (Except DeepSeekHarnessProcessOutcome.RoundError String) := do
  match restoredBytes with
  | .error _ => pure (.error (.request .emptyMessages))
  | .ok restored =>
      match ← executeRestoredBytesOutcome DeepSeekHarnessProcessOutcome.Example.textProcess
          restored "https://fixture.invalid" { value := "fixture-key" } source
          Cordis.Harness.counterConfig 0 [] emptySourcesNodup
          (emptySourcesEarlier restored.restored) with
      | .error error => pure (.error error)
      | .ok ⟨_, ⟨body, _⟩⟩ => pure (.ok body)

end Example

end Cordis.DeepSeekHarnessEventProcessOutcome
