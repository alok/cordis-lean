import Cordis.SessionRefinement

/-!
# Canonical codec for the scalar current-Harness event subset

`SessionRefinement` is intentionally a decoder: it accepts a source-shaped JSON AST, preserves the
wire witness, and rejects fields whose semantics are not represented locally.  This module closes
the opposite direction for a smaller, type-indexed subset.  `encodeWireEvent` only emits canonical
JSON for boundary, route, seed, assistant-chunk, and tool-call events.  Turn-end reasons,
request contexts, surface messages,
request headers, and tool results remain unavailable here because their source fields include
opaque JSON or quarantined metadata.

The `Except` result is the fail-closed boundary: an unsupported `WirePayload` cannot be silently
serialized as a different event.  The main theorem proves that every successful encoding decodes
back to the exact dependent `WireEvent`, including its safe-integer witnesses.  The executable
fixtures additionally check a mixed list through the public list decoder.

This is a canonical AST codec, not a byte/text serializer.  JSON key order, whitespace, UTF-8,
transport framing, and current/future TypeScript object identity remain outside this slice.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement.Codec

open Cordis
open Cordis.SessionRefinement

inductive EncodeError where
  | unsupportedPayload (tag : String)
  deriving DecidableEq, Repr

private def encodePayload (seq time : SafeNat) : WirePayload → Except EncodeError Lean.Json
  | .turnStart turn =>
      .ok (Canonical.turnStart seq time turn)
  | .turnEnd _ _ => .error (.unsupportedPayload "turn/end")
  | .stepStart turn step =>
      .ok (Canonical.stepStart seq time turn step)
  | .stepEnd turn step =>
      .ok (Canonical.stepEnd seq time turn step)
  | .requestContext _ => .error (.unsupportedPayload "request/context")
  | .sessionEndSeed =>
      .ok (Canonical.sessionEndSeed seq time)
  | .assistantChunk chunk =>
      .ok (Canonical.assistantChunk seq time chunk)
  | .assistantReasoningChunk chunk =>
      .ok (Canonical.assistantReasoningChunk seq time chunk)
  | .toolCall turn step callId name arguments =>
      .ok (Canonical.toolCall seq time turn step callId name arguments)
  | .todoWrite _ => .error (.unsupportedPayload "todo/write")
  | .userMessage _ => .error (.unsupportedPayload "user/message")
  | .assistantMessage _ _ _ => .error (.unsupportedPayload "assistant/message")
  | .requestHeader _ => .error (.unsupportedPayload "request/header")
  | .toolResult _ => .error (.unsupportedPayload "tool/result")

/-- Encode only the canonical scalar/control subset; unsupported payloads fail closed. -/
def encodeWireEvent (event : WireEvent) : Except EncodeError Lean.Json :=
  encodePayload event.seq event.time event.payload

example (seq time turn : SafeNat) :
    decodeEvent (Canonical.turnStart seq time turn) =
      .ok { seq, time, payload := .turnStart turn } := by
  exact Canonical.decode_turnStart seq time turn

/-! The public round-trip theorem is stated over successful encodings.  This avoids exposing a
large, redundant `CanonicalWireEvent` predicate: the `Except` result itself is the certificate
that the payload belongs to the emitted subset. -/

theorem decode_encode {event : WireEvent} {json : Lean.Json}
    (encoded : encodeWireEvent event = .ok json) :
    decodeEvent json = .ok event := by
  cases event with
  | mk seq time payload =>
      cases payload with
      | turnStart turn =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_turnStart seq time turn
      | stepStart turn step =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_stepStart seq time turn step
      | stepEnd turn step =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_stepEnd seq time turn step
      | sessionEndSeed =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_sessionEndSeed seq time
      | assistantChunk chunk =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_assistantChunk seq time chunk
      | assistantReasoningChunk chunk =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_assistantReasoningChunk seq time chunk
      | toolCall turn step callId name arguments =>
          simp only [encodeWireEvent, encodePayload] at encoded
          cases encoded
          exact Canonical.decode_toolCall seq time turn step callId name arguments
      | turnEnd _ _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | requestHeader _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | todoWrite _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | requestContext _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | userMessage _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | assistantMessage _ _ _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction
      | toolResult _ =>
          simp only [encodeWireEvent, encodePayload] at encoded
          contradiction

def mixedAssistantChunk : WireAssistantChunk := {
  turn := { value := 1, safe := by decide }
  step := { value := 1, safe := by decide }
  text := "hello"
}

def mixedFixture : List WireEvent := [
  { seq := { value := 1, safe := by decide }, time := { value := 100, safe := by decide },
    payload := .turnStart { value := 1, safe := by decide } },
  { seq := { value := 2, safe := by decide }, time := { value := 101, safe := by decide },
    payload := .stepStart { value := 1, safe := by decide } { value := 1, safe := by decide } },
  { seq := { value := 3, safe := by decide }, time := { value := 102, safe := by decide },
    payload := .assistantChunk mixedAssistantChunk },
  { seq := { value := 4, safe := by decide }, time := { value := 103, safe := by decide },
    payload := .toolCall { value := 1, safe := by decide } { value := 1, safe := by decide }
      "call-0" "lookup" "{\"q\":\"lean\"}" }
]

def mixedFixtureJson : List Lean.Json := mixedFixture.map fun event =>
  match encodeWireEvent event with
  | .ok json => json
  | .error _ => Lean.Json.null

theorem mixedFixture_encodable :
    ∀ event ∈ mixedFixture, ∃ json, encodeWireEvent event = .ok json := by
  intro event member
  simp [mixedFixture] at member
  rcases member with rfl | rfl | rfl | rfl | impossible
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem mixedFixture_decode_encode :
    mixedFixtureJson.mapM decodeEvent = .ok mixedFixture := by
  simp only [mixedFixtureJson, mixedFixture, encodeWireEvent, encodePayload, List.map]
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil]
  simp only [Canonical.decode_turnStart, Canonical.decode_stepStart,
    Canonical.decode_assistantChunk, Canonical.decode_toolCall]
  rfl

end Cordis.SessionRefinement.Codec
