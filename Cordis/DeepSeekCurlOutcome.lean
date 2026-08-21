import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekTerminalOutcome

/-!
# Process-backed DeepSeek terminal outcomes

`DeepSeekTerminalOutcome` classifies a complete in-memory body. This module
connects that dependent sum to the existing deterministic process adapter,
retaining process failures and non-success HTTP statuses separately from a
typed wire/projection rejection. Successful process responses carry the
selected `TerminalOutcome`, whose branch retains the strict SSE certificate.

The fixture uses `sh` and passes the body as one argument; it is executable
adapter evidence, not a claim about shell/curl trust, credentials, network
reachability, incremental delivery, cancellation, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlOutcome

open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekStream
open Cordis.DeepSeekTerminalOutcome

inductive OutcomeClientError where
  | process (error : ProcessError)
  | httpStatus (status : Nat) (body : String)
  | outcome (error : TerminalOutcomeError)
deriving DecidableEq, Repr

structure ProcessedOutcome (body : String) where
  outcome : TerminalOutcome body

def executeOutcome (config : ProcessConfig) (request : HttpRequest) :
    IO (Except OutcomeClientError
      (Sigma fun body : String => ProcessedOutcome body)) := do
  match ← runProcess config request with
  | .error error => pure (.error (.process error))
  | .ok response =>
      if response.status < 200 || response.status ≥ 300 then
        pure (.error (.httpStatus response.status response.body))
      else
        match validateTerminalOutcome response.body with
        | .error error => pure (.error (.outcome error))
        | .ok outcome => pure (.ok ⟨response.body, { outcome }⟩)

def fixtureProcess (body : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-terminal-outcome-fixture",
    body
  ]

def fixtureContentFilter : IO (Except OutcomeClientError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome (fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request

def fixtureText : IO (Except OutcomeClientError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome (fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

def fixtureTool : IO (Except OutcomeClientError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome (fixtureProcess DeepSeekRichToolStream.exampleToolStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

def fixtureMixed : IO (Except OutcomeClientError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome (fixtureProcess DeepSeekRichMixedStream.mixedStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request

def fixtureMulti : IO (Except OutcomeClientError
    (Sigma fun body : String => ProcessedOutcome body)) :=
  executeOutcome (fixtureProcess DeepSeekRichMultiStream.multiBody)
    DeepSeekCurlTransport.fixtureRequest.request

end Cordis.DeepSeekCurlOutcome
