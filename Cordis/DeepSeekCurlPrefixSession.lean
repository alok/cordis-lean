import Cordis.DeepSeekCurlPrefix
import Cordis.DeepSeekSessionRunner

/-!
# Incremental process prefix to typed DeepSeek session

This module closes the semantic step above `DeepSeekCurlPrefix`: a completed process-backed prefix
is projected through one of the accepted text, one-tool, mixed, or multi-call stream languages and
then appended to the proof-carrying session runner. The process response, normalized prefix, wire
certificate, and semantic certificate remain separate fields.

Fuel exhaustion and line-boundary cancellation are returned as typed stops rather than being
misreported as response or stream errors. The bridge still consumes complete lines, and it does not
claim byte framing, asynchronous blocked-read cancellation, backpressure, reconnects, external
execution, provider-complete assembly, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlPrefixSession

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamIncremental

inductive PrefixSessionError where
  | client (error : PrefixClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | fuelExhausted
  | cancelled (line : Nat) (reason : String)
deriving DecidableEq, Repr

structure ProcessedPrefix (policy : LinePolicy) where
  observed : PrefixResponse policy
  wire : DeepSeekStream.ValidatedSseStream observed.state.body
  finished : FinishedResponse observed.state.body

private def requireCompleted
    {policy : LinePolicy}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (response : PrefixResponse policy) : Except PrefixSessionError (ProcessedPrefix policy) :=
  match response.stop with
  | .completed wire =>
      match finish response.state.body with
      | .error error => .error (.response error)
      | .ok finished => .ok { observed := response, wire, finished }
  | .fuelExhausted => .error .fuelExhausted
  | .cancelled line reason _ => .error (.cancelled line reason)

def executeWith
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except PrefixSessionError (ProcessedPrefix policy)) := do
  match ← executeSsePrefix policy maxReads config request with
  | .error error => pure (.error (.client error))
  | .ok response => pure (requireCompleted finish response)

def executeText
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :=
  executeWith finishText policy maxReads config request

def executeTool
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :=
  executeWith finishTool policy maxReads config request

def executeMixed
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :=
  executeWith finishMixed policy maxReads config request

def executeMulti
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :=
  executeWith finishMulti policy maxReads config request

def appendProcessed
    {policy : LinePolicy}
    (runner : Runner)
    (processed : ProcessedPrefix policy)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Runner :=
  Runner.append runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendProcessed_nextSeq
    {policy : LinePolicy}
    (runner : Runner)
    (processed : ProcessedPrefix policy)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  exact Runner.append_nextSeq runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendProcessed_nextCall
    {policy : LinePolicy}
    (runner : Runner)
    (processed : ProcessedPrefix policy)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + processed.finished.finished.view.rawToolCalls.length := by
  exact Runner.append_nextCall runner processed.finished sourceEventSeqs sourcesNodup sourcesEarlier

def executeAndAppend
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except PrefixSessionError (ProcessedPrefix policy × Runner)) := do
  match ← executeWith finish policy maxReads config request with
  | .error error => pure (.error error)
  | .ok processed =>
      pure (.ok (processed,
        appendProcessed runner processed sourceEventSeqs sourcesNodup sourcesEarlier))

def executeAndAppendText
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :=
  executeAndAppend finishText policy maxReads config request runner sourceEventSeqs
    sourcesNodup sourcesEarlier

def fixtureTextProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-prefix-text-fixture",
    DeepSeekRichStream.exampleTextStreamBody
  ]

def fixtureTextResponse : IO (Except PrefixSessionError
    (ProcessedPrefix (LinePolicy.never))) :=
  executeText (LinePolicy.never) 64 fixtureTextProcess DeepSeekCurlTransport.fixtureRequest.request

def fixtureTextAppend : IO (Except PrefixSessionError
    (ProcessedPrefix (LinePolicy.never) × Runner)) :=
  executeAndAppendText (LinePolicy.never) 64 fixtureTextProcess
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) [] (by simp) (by simp)

end Cordis.DeepSeekCurlPrefixSession
