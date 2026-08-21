import Cordis.DeepSeekApi

/-!
# Indexed DeepSeek request modes

`RequestPlan` retains an ordinary `ChatRequest`, which is useful at the raw API boundary but lets
callers accidentally pass a streaming body to a terminal response decoder (or vice versa). This
module adds the small type-indexed certificate needed by the Harness adapters: a
`TypedRequestPlan mode` carries the same plan together with an equality tying its serialized
`stream` flag to `mode`. The existing unindexed builders remain available for compatibility;
mode-specific wrappers are the proof-carrying seam used by newer composition code.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekApi

inductive RequestMode where
  | complete
  | streaming
deriving DecidableEq, Repr

namespace RequestMode

def streamFlag : RequestMode → Bool
  | .complete => false
  | .streaming => true

@[simp] theorem complete_streamFlag : RequestMode.complete.streamFlag = false := rfl

@[simp] theorem streaming_streamFlag : RequestMode.streaming.streamFlag = true := rfl

end RequestMode

namespace ChatRequest

/-- Normalize a request to the terminal, non-streaming variant. -/
def asComplete (request : ChatRequest) : ChatRequest :=
  { request with stream := false }

@[simp] theorem asComplete_stream (request : ChatRequest) :
    (request.asComplete).stream = false := rfl

end ChatRequest

structure TypedRequestPlan (mode : RequestMode) extends RequestPlan where
  stream_eq : toRequestPlan.source.stream = mode.streamFlag

namespace TypedRequestPlan

def requestPlan {mode : RequestMode} (plan : TypedRequestPlan mode) : RequestPlan :=
  plan.toRequestPlan

@[simp] theorem source_stream {mode : RequestMode} (plan : TypedRequestPlan mode) :
    plan.source.stream = mode.streamFlag :=
  plan.stream_eq

@[simp] theorem complete_source_stream (plan : TypedRequestPlan .complete) :
    plan.source.stream = false := by
  exact plan.source_stream

@[simp] theorem streaming_source_stream (plan : TypedRequestPlan .streaming) :
    plan.source.stream = true := by
  exact plan.source_stream

end TypedRequestPlan

def buildTypedRequest
    (mode : RequestMode)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : ChatRequest)
    (stream_eq : source.stream = mode.streamFlag) : TypedRequestPlan mode :=
  { toRequestPlan := buildRequest baseUrl apiKey source
    stream_eq := stream_eq }

def buildTypedCompleteRequest
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    TypedRequestPlan .complete :=
  buildTypedRequest .complete baseUrl apiKey source.asComplete rfl

def buildTypedStreamingRequest
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    TypedRequestPlan .streaming :=
  buildTypedRequest .streaming baseUrl apiKey source.asStreaming rfl

theorem buildTypedCompleteRequest_body_eq
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildTypedCompleteRequest baseUrl apiKey source).request.body =
      Lean.Json.compress source.asComplete.toJson :=
  (buildTypedCompleteRequest baseUrl apiKey source).body_eq

theorem buildTypedStreamingRequest_body_eq
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildTypedStreamingRequest baseUrl apiKey source).request.body =
      Lean.Json.compress source.asStreaming.toJson :=
  (buildTypedStreamingRequest baseUrl apiKey source).body_eq

def executeComplete
    (transport : Transport)
    (plan : TypedRequestPlan .complete) :
    IO (Except ClientError (Sigma fun body : String => ValidatedResponse body)) :=
  execute transport plan.requestPlan

end Cordis.DeepSeekApi
