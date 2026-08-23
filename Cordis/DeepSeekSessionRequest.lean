import Cordis.DeepSeekHarnessExtensions
import Cordis.SessionTheoremBridge
import Cordis.DeepSeekCurlStream

/-!
# Indexed Session.ModelRequest to DeepSeek request handoff

`DeepSeekHarnessExtensions` already builds an OpenAI-compatible request from the projected
session surface.  This module adds the missing type-level seam: a request source must carry an
explicit certificate that its model, system prompt, and encoded tool schemas agree with the
latest `Session.ModelRequest` header.  Optional DeepSeek controls (thinking, reasoning effort,
token limit, response format, tool choice, and error-tool policy) remain adapter policy rather
than being guessed from the generic session header.

The resulting `PreparedRequest` retains the exact `ChatRequest`, the successful builder equation,
the source/header agreement, and the session-message reconstruction equation.  It can be lifted to
raw, complete, or streaming request plans; the mode-indexed variants carry their `stream` flag in
the type.  A complete plan may also be sent through an injected `DeepSeekApi.Transport`, retaining
the API's dependent response validation.  No credential, remote provider, or schema compatibility
claim is made here.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSessionRequest

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekStream
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions

/-! ## Tool-schema encoding certificate -/

structure ToolSchemaEncoder where
  encode : Session.ToolSchema -> ToolDefinition
  name_eq : ∀ schema, (encode schema).function.name = schema.name
  description_eq : ∀ schema, (encode schema).function.description = some schema.description

/-! ## Explicit source/header agreement -/

structure SourceAgreement
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (source : RequestSource)
    (encoder : ToolSchemaEncoder) : Prop where
  model_eq : source.model = request.header.model
  system_eq : source.system = request.header.system
  tools_eq : source.tools = request.header.toolSchemas.map encoder.encode

structure RequestOptions where
  thinking : Option ThinkingMode := none
  reasoningEffort : Option ReasoningEffort := none
  maxTokens : Option Nat := none
  responseFormat : Option ResponseFormat := none
  toolChoice : Option ToolChoice := none
  errorToolResults : ErrorToolResultPolicy := .reject

def sourceFor
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) : RequestSource := {
  model := request.header.model
  system := request.header.system
  thinking := options.thinking
  reasoningEffort := options.reasoningEffort
  maxTokens := options.maxTokens
  responseFormat := options.responseFormat
  tools := request.header.toolSchemas.map encoder.encode
  toolChoice := options.toolChoice
  errorToolResults := options.errorToolResults
}

theorem sourceFor_agreement
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    SourceAgreement request (sourceFor request encoder options) encoder := by
  exact {
    model_eq := rfl
    system_eq := rfl
    tools_eq := rfl
  }

/-! ## Prepared request certificate -/

structure PreparedRequest
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (source : RequestSource)
    (encoder : ToolSchemaEncoder) where
  chat : ChatRequest
  build_eq : buildChatRequestFor source session = .ok chat
  agreement : SourceAgreement request source encoder
  messages_eq : request.messages = session.messages

def prepare
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (source : RequestSource)
    (encoder : ToolSchemaEncoder)
    (agreement : SourceAgreement request source encoder) :
    Except RequestError (PreparedRequest request source encoder) :=
  match h : buildChatRequestFor source session with
  | .error error => .error error
  | .ok chat =>
      .ok {
        chat
        build_eq := h
        agreement
        messages_eq := request.messages_eq
      }

def prepareFromHeader
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    (request : Session.ModelRequest session)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    Except RequestError
      (PreparedRequest request (sourceFor request encoder options) encoder) :=
  prepare request (sourceFor request encoder options) encoder
    (sourceFor_agreement request encoder options)

private theorem chat_model_of_build
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {source : RequestSource}
    {chat : ChatRequest}
    (build_eq : buildChatRequestFor source session = .ok chat) :
    chat.model = source.model := by
  unfold buildChatRequestFor at build_eq
  generalize hconverted :
      sessionMessagesToChatMessagesWith source.errorToolResults
        session.messages = converted at build_eq
  cases converted with
  | error error =>
      dsimp at build_eq
      cases build_eq
  | ok converted =>
      cases hsystem : source.system with
      | none =>
          cases converted with
          | nil =>
              rw [hsystem] at build_eq
              dsimp at build_eq
              cases build_eq
          | cons head tail =>
              rw [hsystem] at build_eq
              dsimp [nonemptyMessages] at build_eq
              cases build_eq
              rfl
      | some system =>
          rw [hsystem] at build_eq
          dsimp at build_eq
          cases build_eq
          rfl

theorem PreparedRequest.chat_model_eq_header
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder) :
    prepared.chat.model = request.header.model := by
  calc
    prepared.chat.model = source.model := chat_model_of_build prepared.build_eq
    _ = request.header.model := prepared.agreement.model_eq

theorem PreparedRequest.source_system_eq_header
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder) :
    source.system = request.header.system :=
  prepared.agreement.system_eq

theorem PreparedRequest.chat_tools_eq_header
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder) :
    source.tools = request.header.toolSchemas.map encoder.encode :=
  prepared.agreement.tools_eq

theorem PreparedRequest.messages_eq_session
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder) :
    request.messages = session.messages :=
  prepared.messages_eq

def buildRequestPlan
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) : RequestPlan :=
  DeepSeekApi.buildRequest baseUrl apiKey prepared.chat

theorem buildRequestPlan_source
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildRequestPlan baseUrl apiKey prepared).source = prepared.chat := rfl

/-! ## Mode-indexed transport plans

The raw `RequestPlan` above is useful for inspecting the JSON body, but it does not prevent a
caller from handing a complete-response request to a streaming decoder (or the reverse).  The
mode-indexed builders below reuse the same certified chat request and add only the existing
`TypedRequestPlan` stream witness.  They still stop before transport, credentials, and provider
behavior.
-/

def buildCompletePlan
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    TypedRequestPlan .complete :=
  DeepSeekApi.buildTypedCompleteRequest baseUrl apiKey prepared.chat

def buildStreamingPlan
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    TypedRequestPlan .streaming :=
  DeepSeekApi.buildTypedStreamingRequest baseUrl apiKey prepared.chat

theorem buildCompletePlan_source
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildCompletePlan baseUrl apiKey prepared).source = prepared.chat.asComplete := rfl

theorem buildStreamingPlan_source
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildStreamingPlan baseUrl apiKey prepared).source = prepared.chat.asStreaming := rfl

theorem buildCompletePlan_model
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildCompletePlan baseUrl apiKey prepared).source.model = request.header.model := by
  rw [buildCompletePlan_source]
  exact prepared.chat_model_eq_header

theorem buildStreamingPlan_model
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildStreamingPlan baseUrl apiKey prepared).source.model = request.header.model := by
  rw [buildStreamingPlan_source]
  exact prepared.chat_model_eq_header

theorem buildCompletePlan_is_complete
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildCompletePlan baseUrl apiKey prepared).source.stream = false :=
  TypedRequestPlan.complete_source_stream _

theorem buildStreamingPlan_is_streaming
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    (buildStreamingPlan baseUrl apiKey prepared).source.stream = true :=
  TypedRequestPlan.streaming_source_stream _

def executeComplete
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    IO (Except ClientError (Sigma fun body : String => ValidatedResponse body)) :=
  DeepSeekApi.execute transport
    (buildCompletePlan baseUrl apiKey prepared).requestPlan

def executeStreamingSse
    {schema : Session.ExtensionSchema}
    {session : Session.Session schema}
    {request : Session.ModelRequest session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder) :
    IO (Except StreamClientError
      (Sigma fun body : String => ValidatedSseStream body)) :=
  DeepSeekCurlStream.executeSse config
    (buildStreamingPlan baseUrl apiKey prepared).request

/-! A deliberately structural encoder for fixtures with no tools.  Real deployments should
provide a parser-backed encoder and prove the `ToolSchema` input-schema contract separately. -/

def structuralToolSchemaEncoder : ToolSchemaEncoder where
  encode schema := {
    function := {
      name := schema.name
      description := some schema.description
      parameters := .mkObj []
      strict := none
    }
  }
  name_eq _ := rfl
  description_eq _ := rfl

end Cordis.DeepSeekSessionRequest
