import Cordis.DeepSeekHarnessLiveProbe
import Cordis.DeepSeekStreamHarnessBytePrefix

/-!
# Credential-safe live streaming probe for the typed DeepSeek Harness

`DeepSeekHarnessLiveProbe` covers the complete-body environment handoff. This module carries the
same credential boundary through the arbitrary-byte streaming path: a caller supplies an
environment-variable name, the key is read without logging, a typed streaming request is built,
and the configured curl process feeds the byte-prefix Harness continuation. The dependent result
retains the prepared request and the complete/fuel-stopped conversation witness together.

The fixture is local and deterministic. The environment path is an executable adapter, not a
proof of credential validity, remote reachability, provider obedience, executable trust,
backpressure, cancellation delivery, retries, persistence, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLiveStreamProbe

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLiveProbe
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarnessBytePrefix

/-! ## Configuration and exact request provenance -/

structure ProbeConfig where
  baseUrl : String
  apiKeyEnvironment : String := "DEEPSEEK_API_KEY"
  source : RequestSource
  fuel : Nat := 1
  maxReads : Nat := 128
  chunkSize : Nat := 256
  curl : CurlConfig := {}

structure PreparedRequest (config : ProbeConfig) (runner : ConversationRunner) where
  key : ApiKey
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan config.baseUrl key config.source runner.session =
    .ok plan

namespace PreparedRequest

theorem build_exact
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    buildTypedStreamingRequestPlan config.baseUrl prepared.key config.source runner.session =
      .ok prepared.plan :=
  prepared.build_eq

theorem streaming_mode
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {config : ProbeConfig} {runner : ConversationRunner}
    (prepared : PreparedRequest config runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRequest

def prepareRequest (config : ProbeConfig) (key : ApiKey) (runner : ConversationRunner) :
    Except RequestError (PreparedRequest config runner) :=
  match built : buildTypedStreamingRequestPlan config.baseUrl key config.source runner.session with
  | .error error => .error error
  | .ok plan => .ok { key, plan, build_eq := built }

def curlProcessConfig (config : CurlConfig) : ProcessConfig where
  command := config.executable
  args := curlArgs config

inductive ProbeError where
  | credential (error : CredentialError)
  | request (error : RequestError)
  | conversation (error : BytePrefixConversationError)

/-! ## Environment-backed execution -/

def runWithKey
    (config : ProbeConfig)
    (key : ApiKey)
    (process : ProcessConfig)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    IO (Except ProbeError
      (Sigma fun _prepared : PreparedRequest config runner =>
        BytePrefixConversationRunResult cfg)) := do
  match prepareRequest config key runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← runConversationMultiBytePrefix config.fuel config.maxReads config.chunkSize
          process config.baseUrl key config.source sourceEventSeqs
          sourcesNodup sourcesEarlier before runner with
      | .error error => pure (.error (.conversation error))
      | .ok result => pure (.ok ⟨prepared, result⟩)

def runFromEnvironment
    (config : ProbeConfig)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    IO (Except ProbeError
      (Sigma fun _prepared : PreparedRequest config runner =>
        BytePrefixConversationRunResult cfg)) := do
  match ← readApiKey config.apiKeyEnvironment with
  | .error error => pure (.error (.credential error))
  | .ok key =>
      runWithKey config key (curlProcessConfig config.curl) cfg before runner sourceEventSeqs
        sourcesNodup sourcesEarlier

/-! ## Deterministic executable evidence -/

namespace Example

def config : ProbeConfig where
  baseUrl := "https://fixture.invalid"
  apiKeyEnvironment := "CORDIS_FIXTURE_STREAM_KEY_NOT_READ"
  source := DeepSeekHarness.counterRequestSource
  fuel := 1
  maxReads := 4096
  chunkSize := 1

def runner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def run : IO (Except ProbeError
    (Sigma fun _prepared : PreparedRequest config runner =>
      BytePrefixConversationRunResult Cordis.Harness.counterConfig)) :=
  runWithKey config { value := "fixture-key" }
    (DeepSeekStreamHarness.streamFlagFixtureProcess
      DeepSeekStreamHarness.counterToolStreamBody)
    Cordis.Harness.counterConfig 0 runner [] List.nodup_nil (fun _ source sourceMem => by
      simp at sourceMem)

def missingCredential : IO Bool := do
  match ← readApiKey "CORDIS_MISSING_STREAM_KEY_9A4B" with
  | .error (.missing _) => pure true
  | .error (.empty _) | .ok _ => pure false

def fixtureSummary : IO Bool := do
  match ← run with
  | .error _ => pure false
  | .ok ⟨prepared, result⟩ =>
      pure (prepared.plan.source.stream == true && result.rounds.length = 1 &&
        result.finalModel = 0 && !BytePrefixConversationStop.isCompleted result.stop)

end Example

end Cordis.DeepSeekHarnessLiveStreamProbe
