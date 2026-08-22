import Cordis.DeepSeekHarnessEventIgnorableRunner
import Cordis.DeepSeekHarnessTransportConversation

/-!
# Transport continuation from a normalized explicit-ignorable event log

`DeepSeekHarnessEventIgnorableRunner` attaches a normalized source log to the pure
`ConversationRunner` and certifies request rebuilding.  This module carries that exact dependent
runner into the existing process-backed, complete-response conversation transport.  The returned
certificate retains the original normalized log, the transport conversation trace, the final
runner/model, and the runner/session equalities; it does not turn a deterministic process fixture
into a provider, credential, persistence, or deployed-Harness equivalence theorem.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventIgnorableTransport

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventIgnorableRunner
open Cordis.DeepSeekHarnessEventIgnorableNormalization
open Cordis.DeepSeekHarnessTransportConversation
open Cordis.DeepSeekHarnessPersistenceTransportRound
open Cordis.DeepSeekCurlTransport

structure RestoredTransportRun
    {input : List Lean.Json}
    {Model Capability : Type}
    (restored : RestoredRunner input)
    (cfg : GenericHarness.Config Model Capability)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (initialModel : Model)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  run : TransportConversationRunResult cfg baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier restored.runner initialModel finalRunner finalModel
  session_eq_final : restored.runner.session = restored.log.validated.final.session
  step_eq_final : restored.runner.step = restored.log.validated.final.session.nextSeq

namespace RestoredTransportRun

theorem session_certificate
    {input : List Lean.Json}
    {Model Capability : Type}
    {restored : RestoredRunner input}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {initialModel : Model}
    {finalRunner : ConversationRunner}
    {finalModel : Model}
    (result : RestoredTransportRun restored cfg baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier initialModel finalRunner finalModel) :
    restored.runner.session = restored.log.validated.final.session :=
  result.session_eq_final

theorem step_certificate
    {input : List Lean.Json}
    {Model Capability : Type}
    {restored : RestoredRunner input}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {initialModel : Model}
    {finalRunner : ConversationRunner}
    {finalModel : Model}
    (result : RestoredTransportRun restored cfg baseUrl apiKey source sourceEventSeqs
      sourcesNodup sourcesEarlier initialModel finalRunner finalModel) :
    restored.runner.step = restored.log.validated.final.session.nextSeq :=
  result.step_eq_final

end RestoredTransportRun

def runRestoredTransport
    {input : List Lean.Json}
    {Model Capability : Type}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (restored : RestoredRunner input)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (initialModel : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RestoredTransportRun restored cfg baseUrl apiKey source sourceEventSeqs
            sourcesNodup sourcesEarlier initialModel finalRunner finalModel)) := do
  match ← runTransport fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier initialModel restored.runner with
  | .error error => pure (.error error)
  | .ok ⟨finalRunner, ⟨finalModel, run⟩⟩ =>
      pure (.ok ⟨finalRunner, ⟨finalModel, {
        run
        session_eq_final := restored.session_eq_final
        step_eq_final := restored.step_eq_final
      }⟩⟩)

def runToolNormalizedTransport
    (restored : RestoredRunner ignorableMiddleToolFixtureJson) :
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RestoredTransportRun restored Cordis.Harness.counterConfig
            "https://fixture.invalid" { value := "fixture-key" }
            { model := "deepseek-reasoner", errorToolResults := .reject }
            [] (by simp) (by
              intro current source sourceMem
              cases sourceMem) 0 finalRunner finalModel)) :=
  runRestoredTransport 1
    (DeepSeekCurlTransport.fixtureTransport DeepSeekHarness.counterFinalResponseBody)
    "https://fixture.invalid" { value := "fixture-key" } restored
    { model := "deepseek-reasoner", errorToolResults := .reject }
    Cordis.Harness.counterConfig 0 [] (by simp) (by
      intro current source sourceMem
      cases sourceMem)

def toolNormalizedTransport
    : IO (Except (NormalizationError ⊕ DeepSeekHarnessPersistenceTransportRound.RoundError)
      (Sigma fun restored : RestoredRunner ignorableMiddleToolFixtureJson =>
        Sigma fun finalRunner : ConversationRunner =>
          Sigma fun finalModel : Nat =>
            RestoredTransportRun restored Cordis.Harness.counterConfig
              "https://fixture.invalid" { value := "fixture-key" }
              { model := "deepseek-reasoner", errorToolResults := .reject }
              [] (by simp) (by
                intro current source sourceMem
                cases sourceMem) 0 finalRunner finalModel)) := do
  match toolNormalizedRunner with
  | .error error => pure (.error (.inl error))
  | .ok restored =>
      let transportResult ← runToolNormalizedTransport restored
      match transportResult with
      | .error error => pure (.error (.inr error))
      | .ok ⟨finalRunner, ⟨finalModel, run⟩⟩ =>
          pure (.ok ⟨restored, ⟨finalRunner, ⟨finalModel, run⟩⟩⟩)

end Cordis.DeepSeekHarnessEventIgnorableTransport
