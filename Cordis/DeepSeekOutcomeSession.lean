import Cordis.DeepSeekCurlOutcome
import Cordis.DeepSeekSessionRunner

/-!
# Proof-carrying terminal outcomes into the local session runner

`DeepSeekCurlOutcome` proves that a complete process response belongs to one of the
supported terminal languages. This module is the next boundary: provider failures are
returned as typed terminal values and leave the local session unchanged, while successful
rich outcomes are finished and appended through `DeepSeekSessionRunner.Runner.append`.

The failure branch intentionally does not fabricate an assistant message. A caller that
wants a retry, an `isError` event, or an application-specific diagnostic must choose that
policy at a later boundary. The process fixture is executable evidence for this local
composition only; it does not establish network, credential, process, or deployed
DeepSeek Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekOutcomeSession

open Cordis
open Cordis.DeepSeekCurlOutcome
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamFailure
open Cordis.DeepSeekTerminalOutcome

inductive DispatchError where
  | bridge (error : DeepSeekSessionBridge.BridgeError)
deriving DecidableEq, Repr

inductive DispatchResult (body : String) where
  | providerFailure
      (validated : ValidatedFailureStream body)
      (runner : Runner)
  | appended
      (finished : FinishedResponse body)
      (runner : Runner)

def dispatchOutcome
    {body : String}
    (runner : Runner)
    (outcome : TerminalOutcome body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DispatchError (DispatchResult body) :=
  match outcome with
  | .failure validated =>
      .ok (.providerFailure validated runner)
  | .text validated =>
      match finishResponse (.text validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.appended finished
            (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .tool validated =>
      match finishResponse (.tool validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.appended finished
            (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .mixed validated =>
      match finishResponse (.mixed validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.appended finished
            (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .multi validated =>
      match finishResponse (.multi validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.appended finished
            (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier))

theorem dispatchOutcome_providerFailure
    {body : String}
    (runner : Runner)
    (validated : ValidatedFailureStream body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    dispatchOutcome runner (.failure validated) sourceEventSeqs sourcesNodup sourcesEarlier =
      .ok (.providerFailure validated runner) := by
  rfl

theorem dispatchOutcome_text_appends
    {body : String}
    (runner : Runner)
    (validated : DeepSeekRichStream.ValidatedTextStream body)
    (finished : FinishedResponse body)
    (finish : finishResponse (.text validated) = .ok finished)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    dispatchOutcome runner (.text validated) sourceEventSeqs sourcesNodup sourcesEarlier =
      .ok (.appended finished
        (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier)) := by
  simp [dispatchOutcome, finish]

theorem append_nextSeq
    {body : String}
    (runner : Runner)
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (Runner.append runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 :=
  Runner.append_nextSeq runner finished sourceEventSeqs sourcesNodup sourcesEarlier

inductive ClientError where
  | transport (error : OutcomeClientError)
  | dispatch (error : DispatchError)
deriving DecidableEq, Repr

def executeAndDispatchOutcome
    (config : DeepSeekCurlTransport.ProcessConfig)
    (request : DeepSeekApi.HttpRequest)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ClientError (Sigma fun body : String => DispatchResult body)) := do
  match ← executeOutcome config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, processed⟩ =>
      match dispatchOutcome runner processed.outcome sourceEventSeqs
          sourcesNodup sourcesEarlier with
      | .error error => pure (.error (.dispatch error))
      | .ok result => pure (.ok ⟨body, result⟩)

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    (runner : Runner) : ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

def fixtureFailureDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

def fixtureTextDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

def fixtureToolDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichToolStream.exampleToolStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

def fixtureMixedDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichMixedStream.mixedStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

def fixtureMultiDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichMultiStream.multiBody)
    DeepSeekCurlTransport.fixtureRequest.request (Runner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

end Cordis.DeepSeekOutcomeSession
