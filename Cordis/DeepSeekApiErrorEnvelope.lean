import Cordis.DeepSeekApi

/-!
# Proof-carrying DeepSeek API-error envelopes

`DeepSeekApi.execute` already distinguishes a non-success HTTP status from a malformed
successful response, but the response body of a provider error was previously retained only as
an untyped `String`. This module validates the OpenAI-compatible `{ "error": ... }` envelope and
keeps the parsed `ApiErrorBody` together with the exact JSON parse/decode equations.

The result is a wire-boundary certificate, not a claim that a provider returned an authentic error
or that a retry is safe. Callers still choose retry, persistence, cancellation, and policy.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekApiErrorEnvelope

open Cordis.DeepSeekApi

inductive ValidationError where
  | invalidJson (message : String)
  | decode (error : ApiDecodeError)
  | notApiError
deriving DecidableEq, Repr

structure ValidatedApiError (body : String) where
  json : Lean.Json
  error : ApiErrorBody
  parsed : Lean.Json.parse body = .ok json
  decoded : decodeResponseJson json = .error (.api error)

def validateApiError (body : String) :
    Except ValidationError (ValidatedApiError body) :=
  match parsed : Lean.Json.parse body with
  | .error message => .error (.invalidJson message)
  | .ok json =>
      match decoded : decodeResponseJson json with
      | .error (.api error) => .ok { json, error, parsed, decoded }
      | .error (.invalidJson message) => .error (.invalidJson message)
      | .error (.decode error) => .error (.decode error)
      | .ok _response => .error .notApiError

theorem validateApiError_decoded
    {body : String} (validated : ValidatedApiError body) :
    decodeResponseJson validated.json = .error (.api validated.error) :=
  validated.decoded

theorem validateApiError_parsed
    {body : String} (validated : ValidatedApiError body) :
    Lean.Json.parse body = .ok validated.json :=
  validated.parsed

def exampleBody : String := Lean.Json.compress (.mkObj [
  ("error", .mkObj [
    ("message", .str "rate limited"),
    ("type", .str "rate_limit_error"),
    ("param", .null),
    ("code", .str "429")
  ])
])

def exampleValidation : Except ValidationError (ValidatedApiError exampleBody) :=
  validateApiError exampleBody

end Cordis.DeepSeekApiErrorEnvelope
