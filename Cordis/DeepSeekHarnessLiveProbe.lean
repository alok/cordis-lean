import Cordis.DeepSeekHarness

/-!
# Credential-safe curl probe for the typed DeepSeek Harness

This module is the explicit runtime handoff after the proof-carrying Harness round.  A caller
supplies a base URL, a `RequestSource`, a bounded fuel value, and the name of an environment
variable.  The pure part turns the current `ConversationRunner` into a complete-mode
`TypedRequestPlan`; the IO part reads the key without logging or storing it in a repository and
can send the plan through the existing argv-only curl adapter.

`runWithKey` is also available for deterministic tests and alternate credential stores.  Its
dependent result retains the exact prepared plan beside the conversation result, so a successful
run cannot erase which session endpoint and complete/streaming mode produced the request.  The
fixture uses the same high-level path with an injected two-response transport.  This does not
claim credential validity, network reachability, provider obedience, process trust, backoff,
idempotency, or deployed DeepSeek Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLiveProbe

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner

/-! ## Credential boundary -/

inductive CredentialError where
  | missing (environment : String)
  | empty (environment : String)
deriving DecidableEq, Repr

def parseApiKey (environment : String) : Option String → Except CredentialError ApiKey
  | none => .error (.missing environment)
  | some value =>
      if value.isEmpty then
        .error (.empty environment)
      else
        .ok { value }

def readApiKey (environment : String) : IO (Except CredentialError ApiKey) := do
  parseApiKey environment <$> IO.getEnv environment

/-! ## Configuration and prepared request -/

structure ProbeConfig where
  baseUrl : String
  apiKeyEnvironment : String := "DEEPSEEK_API_KEY"
  source : RequestSource
  fuel : Nat := 1
  curl : CurlConfig := {}

structure PreparedRequest (config : ProbeConfig) (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .complete
  build_eq : buildTypedCompleteRequestPlan config.baseUrl key config.source runner.session =
    .ok plan

namespace PreparedRequest

theorem build_exact
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    buildTypedCompleteRequestPlan config.baseUrl prepared.key config.source runner.session =
      .ok prepared.plan :=
  prepared.build_eq

theorem complete_mode
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    prepared.plan.source.stream = false :=
  prepared.plan.complete_source_stream

theorem body_eq_source
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    prepared.plan.request.body =
      Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRequest

def prepareRequest (config : ProbeConfig) (key : ApiKey) (runner : ConversationRunner) :
    Except RequestError (PreparedRequest config runner) :=
  match built : buildTypedCompleteRequestPlan config.baseUrl key config.source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

inductive ProbeError where
  | credential (error : CredentialError)
  | request (error : RequestError)
  | conversation (error : ConversationError)
deriving DecidableEq, Repr

/-! ## Transport-backed execution -/

def runWithKey
    (config : ProbeConfig)
    (key : ApiKey)
    (transport : Transport)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except ProbeError
      (Sigma fun _prepared : PreparedRequest config runner =>
        ConversationRunResult cfg)) := do
  match prepareRequest config key runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← DeepSeekHarness.runConversation config.fuel transport config.baseUrl key
          config.source [] List.nodup_nil (fun _ _ h => by cases h) before runner with
      | .error error => pure (.error (.conversation error))
      | .ok result => pure (.ok ⟨prepared, result⟩)

def runFromEnvironment
    (config : ProbeConfig)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except ProbeError
      (Sigma fun _prepared : PreparedRequest config runner =>
        ConversationRunResult cfg)) := do
  match ← readApiKey config.apiKeyEnvironment with
  | .error error => pure (.error (.credential error))
  | .ok key =>
      runWithKey config key (curlTransport config.curl) cfg before runner

/-! ## Deterministic fixture -/

namespace Example

def config : ProbeConfig where
  baseUrl := "https://fixture.invalid"
  apiKeyEnvironment := "CORDIS_FIXTURE_KEY_NOT_READ"
  source := DeepSeekHarness.counterRequestSource
  fuel := 2

def invalidRequestConfig : ProbeConfig :=
  { config with source := { model := "fixture-model" } }

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def twoRoundTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.modify (fun value => value + 1)
    pure (.ok {
      status := 200
      body := if index = 0 then DeepSeekHarness.counterResponseBody
        else DeepSeekHarness.counterFinalResponseBody
    })

structure Summary where
  completeRequest : Bool
  rounds : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  finalModel : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def expectedSummary : Summary := {
  completeRequest := true
  rounds := 2
  initialNextSeq := 1
  finalNextSeq := 4
  finalModel := 0
  completed := true
}

def run : IO (Except ProbeError Summary) := do
  let calls ← IO.mkRef 0
  match ← runWithKey config { value := "fixture-key" } (twoRoundTransport calls)
      Cordis.Harness.counterConfig 0 runner with
  | .error error => pure (.error error)
  | .ok ⟨prepared, result⟩ =>
      pure (.ok {
        completeRequest := prepared.plan.source.stream == false
        rounds := result.rounds.length
        initialNextSeq := runner.session.nextSeq
        finalNextSeq := result.runner.session.nextSeq
        finalModel := result.finalModel
        completed := result.stop.isCompleted
      })

def parseCredentialSummary : List (Except CredentialError ApiKey) := [
  parseApiKey "KEY" none,
  parseApiKey "KEY" (some ""),
  parseApiKey "KEY" (some "fixture-key")
]

def invalidRunner : ConversationRunner := ConversationRunner.empty 1

def invalidRequest : Except RequestError (PreparedRequest invalidRequestConfig invalidRunner) :=
  prepareRequest invalidRequestConfig { value := "fixture-key" } invalidRunner

theorem expectedSummary_complete : expectedSummary.completeRequest = true := rfl

end Example

end Cordis.DeepSeekHarnessLiveProbe
