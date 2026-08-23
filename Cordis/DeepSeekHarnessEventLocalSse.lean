import Cordis.DeepSeekHarnessEventRequest
import Cordis.DeepSeekHarnessLocalSseIndexed

/-!
# Validated current-Harness endpoint through loopback HTTP/SSE

`DeepSeekHarnessEventRequest` ends with a dependent request whose session index is the exact
endpoint of a validated current-Harness JSON log.  This module supplies the small runner frame
needed by the local SSE adapter and sends that same indexed request through the real loopback
curl/Python fixture.  The resulting certificate retains the event log, request, wire frames, and
append endpoint; its sequence theorem is derived from `ExtensionRunner.appendFinished` rather
than from a test counter.

The fixture is intentionally local evidence.  It does not establish remote reachability, TLS,
credential validity, provider authenticity, persistence, reconnects, blocked-read interruption,
or equivalence with the deployed TypeScript Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventLocalSse

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekHarnessEventRequest
open Cordis.DeepSeekHarnessLocalSseIndexed
open Cordis.DeepSeekSessionRequest
open Cordis.DeepSeekSessionRunner

universe u

structure EventRunner
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) where
  turn : Nat
  nextCall : Nat
  toolCallCount_eq_nextCall :
    toolCallCount certificate.log.final.session.messages = nextCall

namespace EventRunner

def extensionRunner
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    (frame : EventRunner certificate) : ExtensionRunner Session.noExtensions := {
  session := certificate.log.final.session
  turn := frame.turn
  step := certificate.log.final.session.nextSeq
  nextCall := frame.nextCall
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := frame.toolCallCount_eq_nextCall
}

theorem extensionRunner_session
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    (frame : EventRunner certificate) :
    (frame.extensionRunner).session = certificate.log.final.session :=
  rfl

end EventRunner

structure EventSseResult
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options)
    (frame : EventRunner certificate) where
  sse : IndexedLocalSseResult (runner := frame.extensionRunner) certificate.prepared

namespace EventSseResult

theorem request_header
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    {frame : EventRunner certificate}
    (result : EventSseResult certificate frame) :
    result.sse.localResult.prepared.plan.source.model = certificate.request.header.model := by
  rw [← result.sse.plan_eq]
  exact buildStreamingPlan_model _ _ certificate.prepared

theorem append_endpoint
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    {frame : EventRunner certificate}
    (result : EventSseResult certificate frame) :
    result.sse.after = ExtensionRunner.appendFinished frame.extensionRunner
      result.sse.localResult.finished [] (by simp) (by simp) :=
  result.sse.append_eq

theorem final_nextSeq
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    {frame : EventRunner certificate}
    (result : EventSseResult certificate frame) :
    result.sse.after.session.nextSeq = certificate.log.final.session.nextSeq + 1 := by
  rw [result.sse.append_eq]
  exact ExtensionRunner.appendFinished_nextSeq frame.extensionRunner
    result.sse.localResult.finished [] (by simp) (by simp)

theorem protocol_projection_before
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {certificate : PreparedLogRequest input encoder options}
    :
    Session.protocolProjection certificate.log.final.session.events =
      certificate.log.sequence.protocolTrace.erase :=
  certificate.protocol_projection_eq_replay

end EventSseResult

private def runWithFinish
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options)
    (frame : EventRunner certificate)
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (key : ApiKey)
    (body : String) :
    IO (Except IndexedLocalSseError (EventSseResult certificate frame)) := do
  match ← DeepSeekHarnessLocalSseIndexed.runWithFinish finish
      (runner := frame.extensionRunner) certificate.prepared key body with
  | .error error => pure (.error error)
  | .ok sse => pure (.ok { sse })

private def runWithKey
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options)
    (frame : EventRunner certificate)
    (key : ApiKey)
    (body : String) :
    IO (Except IndexedLocalSseError (EventSseResult certificate frame)) :=
  runWithFinish certificate frame finishText key body

namespace Example

def certificate : PreparedLogRequest SessionRefinement.headerChunkExampleJson
    structuralToolSchemaEncoder headerOptions :=
  match h : DeepSeekHarnessEventRequest.headerPrepared with
  | .error _ => nomatch h
  | .ok certificate => certificate

def frame : EventRunner certificate where
  turn := 1
  nextCall := toolCallCount certificate.log.final.session.messages
  toolCallCount_eq_nextCall := rfl

def body : String := DeepSeekRichStream.exampleTextStreamBody

def run : IO (Except IndexedLocalSseError (EventSseResult certificate frame)) :=
  runWithKey certificate frame { value := "fixture-key" } body

structure Summary where
  requests : Nat
  validRequests : Nat
  deliveredFrames : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
deriving BEq, DecidableEq, Repr

def summarize (result : EventSseResult certificate frame) : Summary := {
  requests := result.sse.localResult.requests
  validRequests := result.sse.localResult.validRequests
  deliveredFrames := result.sse.localResult.response.wire.frames.length
  initialNextSeq := certificate.log.final.session.nextSeq
  finalNextSeq := result.sse.after.session.nextSeq
}

def expectedSummary : Summary := {
  requests := 1
  validRequests := 1
  deliveredFrames := 3
  initialNextSeq := 6
  finalNextSeq := 7
}

theorem final_nextSeq_expected (result : EventSseResult certificate frame) :
    (summarize result).finalNextSeq = 7 := by
  change result.sse.after.session.nextSeq = 7
  rw [EventSseResult.final_nextSeq result]
  rfl

theorem initial_nextSeq_expected (result : EventSseResult certificate frame) :
    (summarize result).initialNextSeq = 6 := by
  rfl

end Example

end Cordis.DeepSeekHarnessEventLocalSse
