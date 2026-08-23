import Cordis.DeepSeekCurlSession
import Cordis.DeepSeekSessionRequest

/-!
# Indexed request to text-stream append

`DeepSeekSessionRequest` already builds a mode-indexed streaming request and
`DeepSeekCurlSession` already retains a strict SSE wire certificate plus a
finished rich response. This module composes those boundaries with the
schema-indexed `ExtensionRunner`: a successful text-only stream keeps its
streaming plan, wire frames, finished response, and exact append endpoint.

The projection is intentionally narrow. It uses `finishText`, so reasoning,
tool-call, mixed, multi-call, unsupported finish, malformed, and incomplete
streams remain typed rejections at this boundary. Process configuration is
injected; no live network, credential, provider, persistence, or deployed
Harness equivalence claim is made.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSessionRequestStreaming

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekSessionRequest
open Cordis.DeepSeekSessionRunner

inductive StreamingAppendError where
  | transport (error : DeepSeekCurlSession.SessionClientError)
deriving DecidableEq, Repr

structure StreamingAppendResult
    {schema : Session.ExtensionSchema}
    (runner : ExtensionRunner schema)
    (baseUrl : String)
    (apiKey : ApiKey)
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (prepared : PreparedRequest request source encoder)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs, eventSeq < runner.session.nextSeq)
    (body : String) where
  plan : TypedRequestPlan .streaming
  plan_eq : plan = buildStreamingPlan baseUrl apiKey prepared
  processed : DeepSeekCurlSession.ProcessedResponse body
  after : ExtensionRunner schema
  append_eq :
    after = ExtensionRunner.appendFinished runner processed.finished sourceEventSeqs
      sourcesNodup sourcesEarlier

namespace StreamingAppendResult

theorem streaming_plan
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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.plan = buildStreamingPlan baseUrl apiKey prepared :=
  result.plan_eq

theorem stream_mode
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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.plan.source.stream = true := by
  rw [streaming_plan result]
  exact buildStreamingPlan_is_streaming baseUrl apiKey prepared

theorem wire_frames_exact
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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    DeepSeekStream.parseSse body = .ok result.processed.wire.frames :=
  result.processed.wire.parsed

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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.after = ExtensionRunner.appendFinished runner result.processed.finished
      sourceEventSeqs sourcesNodup sourcesEarlier :=
  result.append_eq

theorem after_nextSeq
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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.after.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [result.append_eq]
  exact ExtensionRunner.appendFinished_nextSeq runner result.processed.finished
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem after_nextCall
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
    {body : String}
    {baseUrl : String}
    {apiKey : ApiKey}
    (result : StreamingAppendResult runner baseUrl apiKey prepared sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    result.after.nextCall = runner.nextCall +
      result.processed.finished.finished.view.rawToolCalls.length := by
  rw [result.append_eq]
  exact ExtensionRunner.appendFinished_nextCall runner result.processed.finished
    sourceEventSeqs sourcesNodup sourcesEarlier

end StreamingAppendResult

def executeStreamingTextAndAppend
    {schema : Session.ExtensionSchema}
    {runner : ExtensionRunner schema}
    {request : Session.ModelRequest runner.session}
    {source : RequestSource}
    {encoder : ToolSchemaEncoder}
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (prepared : PreparedRequest request source encoder)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs, eventSeq < runner.session.nextSeq) :
    IO (Except StreamingAppendError
      (Sigma fun body : String => StreamingAppendResult runner baseUrl apiKey prepared
        sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  let plan := buildStreamingPlan baseUrl apiKey prepared
  match ← DeepSeekCurlSession.executeTypedStreamingWith finishText config plan with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, processed⟩ =>
      pure (.ok ⟨body, {
        plan
        plan_eq := by
          rfl
        processed
        after := ExtensionRunner.appendFinished runner processed.finished sourceEventSeqs
          sourcesNodup sourcesEarlier
        append_eq := rfl
      }⟩)

end Cordis.DeepSeekSessionRequestStreaming
