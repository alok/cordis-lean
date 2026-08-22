import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekSchemaTransportRetryCancellation

/-!
# Process-backed heterogeneous schema retry and cancellation

`DeepSeekSchemaTransportRetryCancellation` proves the dependent retry/cancellation
composition for an injected complete-body `Transport`.  This module instantiates that
same API with the repository's direct `IO.Process` adapter.  The shell fixture emits a
transient 503 on its first invocation, a heterogeneous weather/clock response on its
second invocation, and a terminal no-tool response on its third invocation.

The process boundary is intentionally retained in the result as ordinary transport
evidence.  The fixture does not prove network reachability, credential validity,
provider obedience, shell/process trust, in-flight interruption, backoff, idempotency,
persistence, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaProcessRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessRetry
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaTransportRetryCancellation
open Cordis.DeepSeekToolSchema

/-! ## A deterministic process fixture -/

def responseBody (index : Nat) : String :=
  if index = 0 then "busy"
  else if index = 1 then DeepSeekSchemaRegistry.Example.dualResponseBody
  else DeepSeekHarness.counterFinalResponseBody

def responseStatus (index : Nat) : Nat :=
  if index = 0 then 503 else 200

def processConfig (index : Nat) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__%s\\n' \"$1\" \"$2\"",
    "cordis-schema-retry-fixture",
    responseBody index,
    toString (responseStatus index)
  ]

def processRetryTransport (calls : IO.Ref Nat) : Transport where
  send request := do
    let index ← calls.get
    calls.set (index + 1)
    (processTransport (processConfig index)).send request

namespace Example

open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaTransportRetryCancellation.Example

def cancellationRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          SchemaRetryRunResult retryPolicy cancellationPolicy
            (dualRegistryEntries weatherCertificate clockCertificate)
            "https://fixture.invalid" { value := "fixture-key" }
            (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp)
            DeepSeekSchemaHarness.Example.counterRunner 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run cancellationPolicy retryPolicy 2 (processRetryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp) 0
    DeepSeekSchemaHarness.Example.counterRunner

def successRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          SchemaRetryRunResult retryPolicy neverCancellation
            (dualRegistryEntries weatherCertificate clockCertificate)
            "https://fixture.invalid" { value := "fixture-key" }
            (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp)
            DeepSeekSchemaHarness.Example.counterRunner 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run neverCancellation retryPolicy 2 (processRetryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp) 0
    DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaProcessRetryCancellation
