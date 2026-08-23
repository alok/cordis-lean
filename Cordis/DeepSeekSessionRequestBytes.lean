import Cordis.DeepSeekApiBytes
import Cordis.DeepSeekSessionRequest

/-!
# Byte response to indexed session append

`DeepSeekApiBytes` retains the exact response `ByteArray`, its UTF-8 decoding, and the ordinary
`ValidatedResponse` certificate. `DeepSeekSessionRequest` already admits the latter and appends
the accepted assistant view to an indexed `ExtensionRunner`. This module composes those two
boundaries without erasing the bytes: a successful result keeps the original byte witness,
the decoded response, the `acceptValidated` certificate, and the exact indexed append endpoint.

The transport is injected, just as in the string API. This proves a byte-to-session refinement
for the supplied transport; it does not claim network reachability, credential validity, provider
obedience, persistence, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSessionRequestBytes

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiBytes
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekSessionRequest

inductive ByteCompleteAppendError where
  | transport (error : DeepSeekApiBytes.ClientError)
  | response (error : ApiSessionError)

def buildCompleteBytePlan
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    DeepSeekApiBytes.ByteRequestPlan :=
  DeepSeekApiBytes.buildRequest baseUrl apiKey prepared.chat.asComplete

theorem buildCompleteBytePlan_source_stream
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildCompleteBytePlan baseUrl apiKey prepared).plan.source.stream = false := by
  rfl

theorem buildCompleteBytePlan_bodyBytes_eq
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildCompleteBytePlan baseUrl apiKey prepared).bodyBytes =
      (Lean.Json.compress prepared.chat.asComplete.toJson).toUTF8 := by
  rfl

structure ByteCompleteAppendResult
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs, eventSeq < runner.session.nextSeq)
    (body : ByteArray) where
  response : ValidatedResponseBytes body
  accepted : AcceptedApiResponse response.text
  accept_eq : acceptValidated response.validated = .ok accepted
  after : ExtensionRunner schema
  append_eq : after = appendAccepted runner accepted sourceEventSeqs sourcesNodup sourcesEarlier

namespace ByteCompleteAppendResult

theorem decoded_exact
    {schema : Session.ExtensionSchema}
    {runner : ExtensionRunner schema}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    {prepared : PreparedRequest request source encoder}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < runner.session.nextSeq}
    {body : ByteArray}
    (result : ByteCompleteAppendResult runner prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    String.fromUTF8? body = some result.response.text :=
  result.response.decoded

theorem append_endpoint_exact
    {schema : Session.ExtensionSchema}
    {runner : ExtensionRunner schema}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    {prepared : PreparedRequest request source encoder}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < runner.session.nextSeq}
    {body : ByteArray}
    (result : ByteCompleteAppendResult runner prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.after =
      appendAccepted runner result.accepted sourceEventSeqs sourcesNodup sourcesEarlier :=
  result.append_eq

end ByteCompleteAppendResult

def executeCompleteBytesAndAppend
    {schema : Session.ExtensionSchema}
    {runner : ExtensionRunner schema}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (transport : DeepSeekApiBytes.Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs, eventSeq < runner.session.nextSeq) :
    IO (Except ByteCompleteAppendError
      (Sigma fun body : ByteArray => ByteCompleteAppendResult runner prepared sourceEventSeqs
        sourcesNodup sourcesEarlier body)) := do
  match ← DeepSeekApiBytes.execute transport (buildCompleteBytePlan baseUrl apiKey prepared) with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, response⟩ =>
      match acceptedEq : acceptValidated response.validated with
      | .error error => pure (.error (.response error))
      | .ok accepted =>
          pure (.ok ⟨body, {
            response
            accepted
            accept_eq := acceptedEq
            after := appendAccepted runner accepted sourceEventSeqs sourcesNodup sourcesEarlier
            append_eq := rfl
          }⟩)

end Cordis.DeepSeekSessionRequestBytes
