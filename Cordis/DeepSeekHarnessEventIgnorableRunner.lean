import Cordis.DeepSeekHarnessEventIgnorableNormalization
import Cordis.DeepSeekHarness

/-!
# Normalized explicit-ignorable events into the typed DeepSeek runner

`DeepSeekHarnessEventIgnorableNormalization` ends with a validated local session.  This module
attaches that dependent endpoint to the pure `ConversationRunner` and reuses the normal request
builder.  The adapter does not reparse, silently erase opaque data, or authenticate a provider:
the normalized log remains the source certificate and the runner/request equalities are explicit.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventIgnorableRunner

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventIgnorableNormalization
open Cordis.DeepSeekSessionRunner
open Cordis.Session

structure RestoredRunner (input : List Lean.Json) where
  log : NormalizedLog input
  runner : ConversationRunner
  session_eq_final : runner.session = log.validated.final.session
  step_eq_final : runner.step = log.validated.final.session.nextSeq

def restoreRunner
    {input : List Lean.Json}
    (log : NormalizedLog input)
    (turn nextCall : Nat)
    (toolCallCount_eq : DeepSeekSessionRunner.toolCallCount
      log.validated.final.session.messages = nextCall) :
    RestoredRunner input :=
  {
    log
    runner := {
      session := log.validated.final.session
      turn
      step := log.validated.final.session.nextSeq
      nextCall
      toolCallCount_eq_nextCall := toolCallCount_eq
    }
    session_eq_final := rfl
    step_eq_final := rfl
  }

theorem RestoredRunner.session_eq_final_cert
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.session = restored.log.validated.final.session :=
  restored.session_eq_final

theorem RestoredRunner.step_eq_nextSeq
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.step = restored.log.validated.final.session.nextSeq :=
  restored.step_eq_final

structure RequestCertificate
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource) where
  request : ChatRequest
  build_eq : buildChatRequest source restored.runner.session = .ok request

def buildRequestCertificate
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource) :
    Except RequestError (RequestCertificate restored source) :=
  match built : buildChatRequest source restored.runner.session with
  | .error error => .error error
  | .ok request => .ok { request, build_eq := built }

theorem RequestCertificate.build_eq_session
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource)
    (certificate : RequestCertificate restored source) :
    buildChatRequest source restored.log.validated.final.session = .ok certificate.request := by
  rw [← restored.session_eq_final]
  exact certificate.build_eq

def toolNormalizedRunner :
    Except NormalizationError
      (RestoredRunner ignorableMiddleToolFixtureJson) :=
  match ignorableMiddleToolNormalized with
  | .error error => .error error
  | .ok normalized =>
      .ok (restoreRunner normalized 1
        (DeepSeekSessionRunner.toolCallCount normalized.validated.final.session.messages) rfl)

def toolNormalizedRequest :
    Except (NormalizationError ⊕ RequestError)
      (Σ restored : RestoredRunner ignorableMiddleToolFixtureJson,
        RequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject }) :=
  match _runnerResult : toolNormalizedRunner with
  | .error error => .error (.inl error)
  | .ok restored =>
      match _requestResult : buildRequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject } with
      | .error error => .error (.inr error)
      | .ok certificate =>
          .ok ⟨restored, certificate⟩

end Cordis.DeepSeekHarnessEventIgnorableRunner
