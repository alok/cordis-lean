import Cordis.DeepSeekCurlStream
import Cordis.DeepSeekSessionRunner

/-!
# Process-backed DeepSeek SSE to session composition

This module closes the next local adapter gap after `DeepSeekCurlStream`: a complete response body
returned by a configured process is retained together with its strict wire certificate, projected
through one of the accepted rich-stream languages, and made available to the proof-carrying
append-only session runner. The process result and the semantic result remain separate fields, so
callers can inspect both boundaries instead of receiving an erased `Runner` value.

The adapter is intentionally complete-body. It does not claim incremental reads,
backpressure, cancellation, reconnects, provider-complete stream assembly, credential validity,
or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlSession

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekSessionRunner

inductive SessionClientError where
  | transport (error : StreamClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
deriving DecidableEq, Repr

structure ProcessedResponse (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  finished : FinishedResponse body

def executeWith
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (config : ProcessConfig) (request : HttpRequest) :
    IO (Except SessionClientError
      (Sigma fun body : String => ProcessedResponse body)) := do
  match ← executeSse config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, wire⟩ =>
      match finish body with
      | .error error => pure (.error (.response error))
      | .ok finished => pure (.ok ⟨body, { wire, finished }⟩)

def executeText (config : ProcessConfig) (request : HttpRequest) :=
  executeWith finishText config request

def executeTool (config : ProcessConfig) (request : HttpRequest) :=
  executeWith finishTool config request

def executeMixed (config : ProcessConfig) (request : HttpRequest) :=
  executeWith finishMixed config request

def executeMulti (config : ProcessConfig) (request : HttpRequest) :=
  executeWith finishMulti config request

def appendProcessed
    (runner : Runner)
    {body : String}
    (processed : ProcessedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Runner :=
  Runner.append runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendProcessed_nextSeq
    (runner : Runner)
    {body : String}
    (processed : ProcessedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  exact Runner.append_nextSeq runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendProcessed_nextCall
    (runner : Runner)
    {body : String}
    (processed : ProcessedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + processed.finished.finished.view.rawToolCalls.length := by
  exact Runner.append_nextCall runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

def executeAndAppend
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (config : ProcessConfig) (request : HttpRequest)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SessionClientError
      (Sigma fun body : String => ProcessedResponse body × Runner)) := do
  match ← executeWith finish config request with
  | .error error => pure (.error error)
  | .ok ⟨body, processed⟩ =>
      pure (.ok ⟨body, (processed,
        appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier)⟩)

def executeAndAppendText (config : ProcessConfig) (request : HttpRequest)
    (runner : Runner) (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
    executeAndAppend finishText config request runner sourceEventSeqs sourcesNodup sourcesEarlier

def executeAndAppendTool (config : ProcessConfig) (request : HttpRequest)
    (runner : Runner) (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
    executeAndAppend finishTool config request runner sourceEventSeqs sourcesNodup sourcesEarlier

def executeAndAppendMixed (config : ProcessConfig) (request : HttpRequest)
    (runner : Runner) (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
    executeAndAppend finishMixed config request runner sourceEventSeqs sourcesNodup sourcesEarlier

def executeAndAppendMulti (config : ProcessConfig) (request : HttpRequest)
    (runner : Runner) (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
  executeAndAppend finishMulti config request runner sourceEventSeqs sourcesNodup sourcesEarlier

def fixtureTextProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-text-sse-fixture",
    DeepSeekRichStream.exampleTextStreamBody
  ]

def fixtureTextResponse : IO (Except SessionClientError
    (Sigma fun body : String => ProcessedResponse body)) :=
  executeText fixtureTextProcess DeepSeekCurlTransport.fixtureRequest.request

def fixtureTextAppend : IO (Except SessionClientError
    (Sigma fun body : String => ProcessedResponse body × Runner)) :=
  executeAndAppendText fixtureTextProcess DeepSeekCurlTransport.fixtureRequest.request
    (Runner.empty 1) [] (by simp) (by simp)

end Cordis.DeepSeekCurlSession
