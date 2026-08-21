import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekStream

/-!
# Process-backed DeepSeek SSE transport

This module composes the process boundary from `DeepSeekCurlTransport` with the strict in-memory
SSE validator from `DeepSeekStream`. A configured executable is allowed to return a complete
response body; successful 2xx bodies are then validated before any caller can use their frames.

The result is deliberately a complete-body adapter, not a claim about incremental reads,
backpressure, cancellation, reconnects, provider-complete stream assembly, or remote-service
behavior. Those remain separate obligations at the deployed adapter boundary.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlStream

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekStream

inductive StreamClientError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | stream (error : StreamError)
deriving DecidableEq, Repr

def executeSse (config : ProcessConfig) (request : HttpRequest) :
    IO (Except StreamClientError
      (Sigma fun body : String => ValidatedSseStream body)) := do
  match ← runProcess config request with
  | .error error => pure (.error (.process error))
  | .ok response =>
      if response.status < 200 || response.status ≥ 300 then
        pure (.error (.httpStatus response.status response.body))
      else
        match validateSse response.body with
        | .error error => pure (.error (.stream error))
        | .ok validated => pure (.ok ⟨response.body, validated⟩)

def curlProcess (config : CurlConfig := {}) : ProcessConfig where
  command := config.executable
  args := curlArgs config

def fixtureProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-sse-fixture",
    DeepSeekStream.exampleStreamBody
  ]

def fixtureResponse : IO (Except StreamClientError
    (Sigma fun body : String => ValidatedSseStream body)) :=
  executeSse fixtureProcess DeepSeekCurlTransport.fixtureRequest.request

end Cordis.DeepSeekCurlStream
