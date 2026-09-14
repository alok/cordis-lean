import Cordis.DeepSeekRequestMode

/-!
# A typed request adapter for the pinned Harness serializer

This adapter targets DeepSeek Harness `99f6f02`'s `serializeRequest` conventions.
The generic API encoder remains available separately. The body certificate proves
the exact local encoding; differential tests supply finite upstream evidence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessCompatibility

open Cordis.DeepSeekApi

/-- The common fragment rejects fields with no counterpart in this Harness adapter. -/
def isSupported (source : ChatRequest) : Bool :=
  source.responseFormat.isNone && source.toolChoice.isNone &&
    source.tools.all (fun tool ↦ tool.function.strict.isNone) &&
    !(source.thinking == some .disabled && source.reasoningEffort.isSome)

/-- Normalize the text-only semantics used by the Harness wire serializer. -/
def normalizeMessage : ChatMessage → ChatMessage
  | .assistant content reasoning calls =>
      .assistant (some (content.getD ""))
        (if calls.isEmpty || reasoning == some "" then none else reasoning) calls
  | .tool id content => .tool id (if content.isEmpty then "(no output)" else content)
  | message => message

/-- Explicit effort enables thinking, as in the pinned provider adapter. -/
def normalizeSource (source : ChatRequest) : ChatRequest := {
  source with
  stream := true
  thinking := if source.reasoningEffort.isSome then some .enabled else source.thinking
  messages := {
    head := normalizeMessage source.messages.head
    tail := source.messages.tail.map normalizeMessage
  }
}

@[simp] theorem normalizeSource_tools (source : ChatRequest) :
    (normalizeSource source).tools = source.tools := rfl

@[simp] theorem normalizeSource_stream (source : ChatRequest) :
    (normalizeSource source).stream = true := rfl

private def omitEmptyCalls (message : Lean.Json) : Lean.Json :=
  match message with
  | .obj fields => .mkObj (fields.toList.filter fun (key, value) ↦
      !(key == "tool_calls" && value == .arr #[]))
  | value => value

/-- Preserve all generic request fields, adapting only the documented Harness conventions. -/
def toJson (source : ChatRequest) : Lean.Json :=
  match (normalizeSource source).toJson with
  | .obj fields => .mkObj (
      fields.toList.map (fun (key, value) ↦
        if key == "messages" then
          (key, match value with
            | .arr messages => .arr (messages.map omitEmptyCalls)
            | other => other)
        else (key, value)) ++
      [("stream_options", .mkObj [("include_usage", .bool true)])])
  | value => value

/-- The transport retains its typed base and an exact equation for the adapted HTTP request. -/
structure CompatibleRequestPlan (original : ChatRequest) where
  supported : isSupported original = true
  base : TypedRequestPlan .streaming
  source_eq : base.source = normalizeSource original
  request : HttpRequest
  request_eq : request = { base.request with body := (toJson original).compress }

namespace CompatibleRequestPlan

theorem source_tools {original : ChatRequest} (plan : CompatibleRequestPlan original) :
    plan.base.source.tools = original.tools := by
  rw [plan.source_eq]
  rfl

theorem body_eq {original : ChatRequest} (plan : CompatibleRequestPlan original) :
    plan.request.body = (toJson original).compress := by
  rw [plan.request_eq]

theorem url_eq {original : ChatRequest} (plan : CompatibleRequestPlan original) :
    plan.request.url = plan.base.request.url := by
  rw [plan.request_eq]

theorem headers_eq {original : ChatRequest} (plan : CompatibleRequestPlan original) :
    plan.request.headers = plan.base.request.headers := by
  rw [plan.request_eq]

end CompatibleRequestPlan

/-- Reject unsupported requests before constructing a proof-carrying transport plan. -/
def buildRequest (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    Except String (CompatibleRequestPlan source) :=
  if h : isSupported source = true then
    let base := buildTypedStreamingRequest baseUrl apiKey (normalizeSource source)
    .ok {
      supported := h
      base
      source_eq := rfl
      request := { base.request with body := (toJson source).compress }
      request_eq := rfl
    }
  else .error "unsupported Harness compatibility request"

end Cordis.DeepSeekHarnessCompatibility
