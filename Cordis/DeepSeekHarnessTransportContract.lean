import Cordis.DeepSeekHarnessProcess
import Cordis.DeepSeekApiSession

/-!
# Proof-carrying request/transport/session composition

`DeepSeekHarnessProcess` keeps request provenance through a configured local process.  This
module closes the parallel pure `DeepSeekApi.Transport` seam: a successful round retains the
prepared request, the exact HTTP response, the response decoder certificate, the accepted
singleton assistant response, and the appended session endpoint in one dependent result.

The adapter validates the response once, retains that decoder certificate, and applies the
strict `acceptValidated` session-language admission to the same dependent value.  A theorem
identifies the accepted value's decoder certificate with the retained transport certificate.
Request construction, transport failure, HTTP status, response decoding, and session admission
remain distinct typed errors.  No field asserts network reachability, credential validity,
provider obedience, external tool execution, or equivalence to a deployed Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportContract

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessProcess
open Cordis.DeepSeekSessionRunner

/-! ## Response/session certificate -/

structure TransportRound
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : Runner}
    (prepared : PreparedRequest baseUrl apiKey source runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq)
    (body : String) where
  response : HttpResponse
  body_eq : response.body = body
  validated : ValidatedResponse body
  accepted : AcceptedApiResponse body
  accepted_validated_eq : accepted.validated = validated
  accepted_eq : acceptValidated validated = .ok accepted
  after : Runner
  append_eq : after = Runner.appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier

namespace TransportRound

theorem response_body_eq
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.response.body = body :=
  round.body_eq

theorem validated_response_eq
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.accepted.validated = round.validated :=
  round.accepted_validated_eq

theorem accepted_response_eq
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    acceptValidated round.validated = .ok round.accepted :=
  round.accepted_eq

theorem append_endpoint
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after = Runner.appendApi runner round.accepted sourceEventSeqs sourcesNodup
      sourcesEarlier :=
  round.append_eq

theorem nextSeq
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [round.append_eq]
  exact Runner.appendApi_nextSeq runner round.accepted sourceEventSeqs sourcesNodup sourcesEarlier

theorem nextCall
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource} {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body) :
    round.after.nextCall = runner.nextCall +
      round.accepted.validated.response.choices.head.message.toolCalls.length := by
  rw [round.append_eq]
  exact Runner.appendApi_nextCall runner round.accepted sourceEventSeqs sourcesNodup sourcesEarlier

end TransportRound

/-! ## Typed errors and execution -/

inductive RoundError where
  | request (error : RequestError)
  | transport (message : String)
  | httpStatus (status : Nat) (body : String)
  | response (error : DeepSeekApi.ResponseError)
  | session (error : ApiSessionError)
deriving DecidableEq, Repr

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

theorem acceptValidated_validated
    {body : String}
    {validated : ValidatedResponse body}
    {accepted : AcceptedApiResponse body}
    (accepted_eq : acceptValidated validated = .ok accepted) :
    accepted.validated = validated := by
  unfold acceptValidated at accepted_eq
  split at accepted_eq <;> try contradiction
  split at accepted_eq <;> try contradiction
  split at accepted_eq <;> try contradiction
  split at accepted_eq <;> try contradiction
  all_goals try (split at accepted_eq <;> try contradiction)
  all_goals
    cases accepted_eq
    rfl

def executePrepared
    (transport : Transport)
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : Runner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun body : String =>
        TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  match ← transport.send prepared.plan.request with
  | .error message => pure (.error (.transport message))
  | .ok response =>
      if successfulStatus response.status then
        match _validatedEq : validateResponse response.body with
        | .error error => pure (.error (.response error))
        | .ok validated =>
            match acceptedEq : acceptValidated validated with
            | .error error => pure (.error (.session error))
            | .ok accepted =>
                have acceptedValidatedEq : accepted.validated = validated :=
                  acceptValidated_validated acceptedEq
                pure (.ok ⟨response.body, {
                  response
                  body_eq := rfl
                  validated
                  accepted
                  accepted_validated_eq := acceptedValidatedEq
                  accepted_eq := acceptedEq
                  after := Runner.appendApi runner accepted sourceEventSeqs sourcesNodup
                    sourcesEarlier
                  append_eq := rfl
                }⟩)
      else
        pure (.error (.httpStatus response.status response.body))

def executeSource
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun prepared : PreparedRequest baseUrl apiKey source runner =>
        Sigma fun body : String =>
          TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  match prepareRequest baseUrl apiKey source runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePrepared transport sourceEventSeqs sourcesNodup sourcesEarlier with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ => pure (.ok ⟨prepared, ⟨body, round⟩⟩)

/-! ## Deterministic transport fixtures -/

namespace Example

def source : RequestSource where
  model := "fixture-model"
  system := some "Only accept the certified local response language."

def transport : Transport :=
  DeepSeekCurlTransport.fixtureTransport DeepSeekApi.exampleResponseBody

def round : IO (Except RoundError
    (Sigma fun prepared : PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
      source (Runner.empty 1) =>
      Sigma fun body : String =>
        TransportRound prepared [] (by simp) (by simp) body)) :=
  executeSource transport "https://fixture.invalid" { value := "fixture-key" }
    source (Runner.empty 1) [] (by simp) (by simp)

def statusFailureTransport : Transport := {
  send := fun _ => pure (.ok { status := 503, body := "busy" })
}

def statusFailure : IO (Except RoundError
    (Sigma fun prepared : PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
      source (Runner.empty 1) =>
      Sigma fun body : String =>
        TransportRound prepared [] (by simp) (by simp) body)) :=
  executeSource statusFailureTransport "https://fixture.invalid" { value := "fixture-key" }
    source (Runner.empty 1) [] (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessTransportContract
