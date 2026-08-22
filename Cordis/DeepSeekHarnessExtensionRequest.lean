import Cordis.DeepSeekHarnessExtensionArchive
import Cordis.DeepSeekToolSchema

/-!
# Certified requests from schema-indexed extension archives

`DeepSeekHarnessExtensionArchive` restores an indexed session and can rebuild a request from it.
This module adds the adjacent request-side certificate: a request is reconstructed only when the
caller also supplies `DeepSeekToolSchema.CertifiedRequestSource`, so malformed or duplicate tool
definitions cannot be hidden behind an otherwise valid extension archive.

The certificate preserves the exact source, validated tool-list proof, indexed session, and
request-builder equation. It does not prove provider-side schema obedience, transport, credentials,
or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessExtensionRequest

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensionArchive
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekToolSchema

/-- A request whose tool source and indexed extension session are both certified. -/
structure CertifiedRequest
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input))
    (source : RequestSource) where
  tools : DeepSeekToolSchema.CertifiedRequestSource source
  request : DeepSeekApi.ChatRequest
  build_eq : buildChatRequestFor source restored.runner.session = .ok request

def buildCertifiedRequest
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input))
    (source : RequestSource) :
    Except (DeepSeekToolSchema.ToolSchemaError ⊕ RequestError)
      (CertifiedRequest restored source) :=
  match validateRequestSource source with
  | .error error => .error (.inl error)
  | .ok tools =>
      match buildRequestCertificate restored source with
      | .error error => .error (.inr error)
      | .ok certificate =>
          .ok {
            tools,
            request := certificate.request,
            build_eq := certificate.build_eq
          }

theorem CertifiedRequest.build_eq_archive
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    {restored : RestoredRunner (codec := codec) (initial := initial) (input := input)}
    {source : RequestSource}
    (certificate : CertifiedRequest restored source) :
    buildChatRequestFor source restored.archive.validated.final = .ok certificate.request := by
  exact buildRequest_session_eq_archive restored source certificate.build_eq

theorem CertifiedRequest.tool_names_nodup
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    {restored : RestoredRunner (codec := codec) (initial := initial) (input := input)}
    {source : RequestSource}
    (certificate : CertifiedRequest restored source) :
    (source.tools.map (fun tool => tool.function.name)).Nodup :=
  certificate.tools.names_nodup

namespace Example

open DeepSeekHarnessExtensionArchive.Example

def certifiedExampleRequest
    (restored : RestoredRunner (codec := SessionExtensionRefinement.Example.exampleCodec)
      (initial := Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      (input := SessionExtensionRefinement.Example.exampleInput)) :
    Except (DeepSeekToolSchema.ToolSchemaError ⊕ RequestError)
      (CertifiedRequest restored exampleSource) :=
  buildCertifiedRequest restored exampleSource

theorem certified_example_request_shape :
    (match restoredExample with
    | .error _ => none
    | .ok restored =>
        match certifiedExampleRequest restored with
        | .error _ => none
        | .ok certificate =>
            some (certificate.request.model, certificate.request.messages.toList)) =
      some ("deepseek-chat", [DeepSeekApi.ChatMessage.user "extension:ready"]) := by
  rfl

def duplicateExampleRequest
    (restored : RestoredRunner (codec := SessionExtensionRefinement.Example.exampleCodec)
      (initial := Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      (input := SessionExtensionRefinement.Example.exampleInput)) :
    Except (DeepSeekToolSchema.ToolSchemaError ⊕ RequestError)
      (CertifiedRequest restored DeepSeekToolSchema.duplicateNamesSource) :=
  buildCertifiedRequest restored DeepSeekToolSchema.duplicateNamesSource

theorem duplicate_example_rejected :
    (match restoredExample with
    | .error _ => none
    | .ok restored =>
        match duplicateExampleRequest restored with
        | .error error => some error
        | .ok _ => none) =
      some (.inl (.duplicateToolName "get_weather")) := by
  rfl

end Example

end Cordis.DeepSeekHarnessExtensionRequest
