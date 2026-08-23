import Cordis.DeepSeekApi

/-!
# Byte-backed DeepSeek API boundary

`DeepSeekApi` models a small OpenAI-compatible request/response subset over strings. This
module makes the byte boundary explicit: request plans retain the exact UTF-8 bytes of the
canonical JSON body, successful byte responses retain their decoded text and typed response
certificate, and non-UTF-8 or non-2xx bodies remain distinct errors.

The executor uses an injected byte transport. It does not claim network reachability, credential
validity, provider obedience, tool-process execution, or deployed DeepSeek Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekApiBytes

open Cordis.DeepSeekApi

/-! ## Exact request bytes -/

structure ByteRequestPlan where
  plan : RequestPlan
  bodyBytes : ByteArray
  bodyBytes_eq : bodyBytes = plan.request.body.toUTF8

def buildRequest
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) : ByteRequestPlan :=
  let plan := DeepSeekApi.buildRequest baseUrl apiKey source
  {
    plan
    bodyBytes := plan.request.body.toUTF8
    bodyBytes_eq := rfl
  }

def buildStreamingRequest
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) : ByteRequestPlan :=
  let plan := DeepSeekApi.buildStreamingRequest baseUrl apiKey source
  {
    plan
    bodyBytes := plan.request.body.toUTF8
    bodyBytes_eq := rfl
  }

theorem ByteRequestPlan.bodyBytes_exact (request : ByteRequestPlan) :
    request.bodyBytes = request.plan.request.body.toUTF8 :=
  request.bodyBytes_eq

theorem buildRequest_bodyBytes_eq
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildRequest baseUrl apiKey source).bodyBytes =
      (Lean.Json.compress source.toJson).toUTF8 := by
  rfl

theorem buildStreamingRequest_bodyBytes_eq
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildStreamingRequest baseUrl apiKey source).bodyBytes =
      (Lean.Json.compress source.asStreaming.toJson).toUTF8 := by
  rfl

theorem buildStreamingRequest_source_stream
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildStreamingRequest baseUrl apiKey source).plan.source.stream = true := by
  rfl

/-! ## Exact response bytes -/

inductive ByteResponseError where
  | invalidUtf8
  | response (error : ResponseError)
deriving DecidableEq, Repr

structure ValidatedResponseBytes (source : ByteArray) where
  text : String
  decoded : String.fromUTF8? source = some text
  validated : ValidatedResponse text

def validateResponseBytes (source : ByteArray) :
    Except ByteResponseError (ValidatedResponseBytes source) :=
  match decoded : String.fromUTF8? source with
  | none => .error .invalidUtf8
  | some text =>
      match _validated : validateResponse text with
      | .error error => .error (.response error)
      | .ok result => .ok { text, decoded, validated := result }

namespace ValidatedResponseBytes

theorem decoded_exact {source : ByteArray} (validated : ValidatedResponseBytes source) :
    String.fromUTF8? source = some validated.text :=
  validated.decoded

theorem parsed_exact {source : ByteArray} (validated : ValidatedResponseBytes source) :
    Lean.Json.parse validated.text = .ok validated.validated.json :=
  validated.validated.parsed

theorem decodedResponse_exact {source : ByteArray}
    (validated : ValidatedResponseBytes source) :
    decodeResponseJson validated.validated.json = .ok validated.validated.response :=
  validated.validated.decoded

end ValidatedResponseBytes

/-! ## Injected byte transport -/

structure HttpResponse where
  status : Nat
  body : ByteArray

structure Transport where
  send : HttpRequest → IO (Except String HttpResponse)

inductive ClientError where
  | transport (message : String)
  | invalidUtf8 (status : Nat) (body : ByteArray)
  | httpStatus (status : Nat) (body : ByteArray)
  | response (error : ResponseError)

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

def execute
    (transport : Transport)
    (plan : ByteRequestPlan) :
    IO (Except ClientError (Σ body : ByteArray, ValidatedResponseBytes body)) := do
  match ← transport.send plan.plan.request with
  | .error message => pure (.error (.transport message))
  | .ok response =>
      if successfulStatus response.status then
        match validateResponseBytes response.body with
        | .error .invalidUtf8 => pure (.error (.invalidUtf8 response.status response.body))
        | .error (.response error) => pure (.error (.response error))
        | .ok validated => pure (.ok ⟨response.body, validated⟩)
      else
        pure (.error (.httpStatus response.status response.body))

/-! ## Deterministic byte fixture -/

def exampleRequest : ByteRequestPlan :=
  buildRequest "https://api.deepseek.com" { value := "fixture-key" } DeepSeekApi.exampleRequest

def exampleResponseBytes : ByteArray := DeepSeekApi.exampleResponseBody.toUTF8

def exampleTransport : Transport where
  send _request := pure <| .ok {
    status := 200
    body := exampleResponseBytes
  }

def exampleRun : IO Bool := do
  match ← execute exampleTransport exampleRequest with
  | .error _ => pure false
  | .ok ⟨body, validated⟩ =>
      pure (body = exampleResponseBytes &&
        validated.validated.response.id == DeepSeekApi.exampleResponse.id &&
        validated.validated.response.choices.head.message.toolCalls.length = 1)

theorem exampleRequest_bodyBytes_exact :
    exampleRequest.bodyBytes = (Lean.Json.compress DeepSeekApi.exampleRequest.toJson).toUTF8 := by
  rfl

end Cordis.DeepSeekApiBytes
