import Cordis.RuntimeRefinement
import Cordis.SessionValidation

/-!
# Stateful current-Harness session refinement

This module refines a source-shaped subset of DeepSeek Harness `SessionEvent` JSON at upstream
commit `99f6f02` into both local `Session` append witnesses and local intrinsic `Protocol` events.
The current upstream envelope is `{ type, seq, time, data, ignorable?, sourceEventSeqs?,
surfaceOp? }`; this decoder retains `seq` and `time`, rejects `ignorable`, and admits surface
metadata only for the supported append-only tool-result shape.

The translation synthesizes only values fixed by the accepted prefix and named normalizations:

* upstream steps begin at one; local protocol steps begin at zero, so `n + 1` maps to `n`;
* `turn/end` has no upstream `nextStep`; it is read from the validated local `.turn` state;
* provider string call ids receive the next fresh local numeric id and remain in a certified map;
* absent tool-result `isError` becomes `false`, matching the TypeScript optional Boolean default.

The supported event vocabulary is turn/step boundaries, tool calls, and a restricted tool result
whose three call-id occurrences agree and whose nested result content is exactly one text block.
Only upstream `completed` and `max-tokens` turn-end reasons map without information loss.

User and assistant messages, assistant chunks, request headers/context, replacement surface ops,
tool-result error identity/meta, multimodal or multi-block tool results, and all extension events
are rejected. Their upstream payloads contain identities, provenance, replay data, arbitrary JSON,
or modalities absent from the local types. The wire witness retains upstream `time`; the local
session has no timestamp field, so no local projection claim mentions it. This is a sound
supported-subset refinement, not a
behavioral-equivalence claim or a general current/future session-log reader. JSON text parsing,
UTF-8, timestamps as wall-clock facts, persistence framing, and storage recovery remain outside.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev JsonKind := RuntimeRefinement.JsonKind

/-- Path-aware failures while decoding the supported current session-event subset. -/
inductive DecodeError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | invalidLength (path : List PathSegment) (expected actual : Nat)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | unsupportedField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Nat)
  deriving BEq, DecidableEq, Repr

/-- Turn-end reasons shared without loss by the upstream and local vocabularies. -/
inductive WireTurnEndReason where
  | completed
  | maxTokens
  deriving BEq, DecidableEq, Repr

namespace WireTurnEndReason

def toLocal : WireTurnEndReason → Session.TurnEndReason
  | .completed => .completed
  | .maxTokens => .maxTokens

end WireTurnEndReason

/-- Restricted, still source-shaped fields of one current upstream tool result. -/
structure WireToolResult where
  turn : SafeNat
  step : SafeNat
  messageId : String
  sourceCallId : String
  blockCallId : String
  content : String
  isError : Bool
  sourceEventSeqs : List SafeNat
  deriving DecidableEq, Repr

/-- Supported payloads selected by the current upstream event `type`. -/
inductive WirePayload where
  | turnStart (turn : SafeNat)
  | turnEnd (turn : SafeNat) (reason : WireTurnEndReason)
  | stepStart (turn step : SafeNat)
  | stepEnd (turn step : SafeNat)
  | toolCall (turn step : SafeNat) (providerCallId name arguments : String)
  | toolResult (result : WireToolResult)
  deriving DecidableEq, Repr

/-- Current upstream outer event envelope with retained sequence and timestamp. -/
structure WireEvent where
  seq : SafeNat
  time : SafeNat
  payload : WirePayload
  deriving DecidableEq, Repr

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def indexPath (path : List PathSegment) (index : Nat) : List PathSegment :=
  path ++ [.index index]

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def requireField (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def rejectPresent (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError Unit :=
  if (field? json name).isSome then
    .error (.unsupportedField path name)
  else
    .ok ()

private def decodeString (path : List PathSegment) : Lean.Json → Except DecodeError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeBool (path : List PathSegment) : Lean.Json → Except DecodeError Bool
  | .bool value => .ok value
  | json => .error (.typeMismatch path "boolean" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json → Except DecodeError SafeNat
  | .num ⟨Int.ofNat value, 0⟩ =>
      if safe : value ≤ RuntimeRefinement.maxSafeInteger then
        .ok { value, safe }
      else
        .error (.unsafeInteger path value)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError String := do
  decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError SafeNat := do
  decodeSafeNat (fieldPath path name) (← requireField json path name)

private def decodeOptionalBool (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option Bool) :=
  match field? json name with
  | none => .ok none
  | some value => return some (← decodeBool (fieldPath path name) value)

private def decodeSafeNatList (path : List PathSegment) : Lean.Json →
    Except DecodeError (List SafeNat)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except DecodeError (List SafeNat)
        | _, [] => .ok []
        | index, value :: rest => do
            let decoded ← decodeSafeNat (indexPath path index) value
            let suffix ← loop (index + 1) rest
            .ok (decoded :: suffix)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeSingleton (path : List PathSegment) : Lean.Json →
    Except DecodeError Lean.Json
  | .arr values =>
      match values.toList with
      | [value] => .ok value
      | values => .error (.invalidLength path 1 values.length)
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def expectTag (path : List PathSegment) (expected actual : String) :
    Except DecodeError Unit :=
  if actual = expected then
    .ok ()
  else
    .error (.unsupportedTag path actual)

private def rejectSurfaceMetadata (json : Lean.Json) (path : List PathSegment) :
    Except DecodeError Unit := do
  rejectPresent json path "surfaceOp"
  rejectPresent json path "sourceEventSeqs"

private def decodeTurnEndReason (path : List PathSegment) : Lean.Json →
    Except DecodeError WireTurnEndReason
  | json@(.obj _) => do
      let kind ← decodeRequiredString json path "kind"
      match kind with
      | "completed" => .ok .completed
      | "max-tokens" => .ok .maxTokens
      | kind => .error (.unsupportedTag (fieldPath path "kind") kind)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeTextBlock (path : List PathSegment) : Lean.Json → Except DecodeError String
  | json@(.obj _) => do
      expectTag (fieldPath path "type") "text" (← decodeRequiredString json path "type")
      decodeRequiredString json path "text"
  | json => .error (.typeMismatch path "object" (jsonKind json))

private structure DecodedToolResultBlock where
  callId : String
  content : String
  isError : Bool

private def decodeToolResultBlock (path : List PathSegment) : Lean.Json →
    Except DecodeError DecodedToolResultBlock
  | json@(.obj _) => do
      expectTag (fieldPath path "type") "tool-result"
        (← decodeRequiredString json path "type")
      let callId ← decodeRequiredString json path "toolCallId"
      let contentJson ← decodeSingleton (fieldPath path "content")
        (← requireField json path "content")
      let content ← decodeTextBlock (indexPath (fieldPath path "content") 0) contentJson
      let isError ← decodeOptionalBool json path "isError"
      .ok { callId, content, isError := isError.getD false }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeToolResultData (event : Lean.Json) (eventPath : List PathSegment)
    (data : Lean.Json) (dataPath : List PathSegment) : Except DecodeError WireToolResult := do
  rejectPresent data dataPath "error"
  rejectPresent data dataPath "meta"
  let turn ← decodeRequiredNat data dataPath "turn"
  let step ← decodeRequiredNat data dataPath "step"
  let message ← requireField data dataPath "message"
  let messagePath := fieldPath dataPath "message"
  match message with
  | .obj _ =>
      let messageId ← decodeRequiredString message messagePath "id"
      expectTag (fieldPath messagePath "role") "user"
        (← decodeRequiredString message messagePath "role")
      let source ← requireField message messagePath "source"
      let sourcePath := fieldPath messagePath "source"
      let sourceCallId ← match source with
        | .obj _ => do
            expectTag (fieldPath sourcePath "kind") "tool"
              (← decodeRequiredString source sourcePath "kind")
            decodeRequiredString source sourcePath "callId"
        | json => .error (.typeMismatch sourcePath "object" (jsonKind json))
      let blockJson ← decodeSingleton (fieldPath messagePath "content")
        (← requireField message messagePath "content")
      let block ← decodeToolResultBlock
        (indexPath (fieldPath messagePath "content") 0) blockJson
      let surfaceOp ← decodeRequiredString event eventPath "surfaceOp"
      expectTag (fieldPath eventPath "surfaceOp") "append" surfaceOp
      let sources ← decodeSafeNatList (fieldPath eventPath "sourceEventSeqs")
        (← requireField event eventPath "sourceEventSeqs")
      .ok {
        turn, step, messageId, sourceCallId
        blockCallId := block.callId
        content := block.content
        isError := block.isError
        sourceEventSeqs := sources
      }
  | json => .error (.typeMismatch messagePath "object" (jsonKind json))

private def decodePayload (event : Lean.Json) (path : List PathSegment)
    (tag : String) (data : Lean.Json) : Except DecodeError WirePayload :=
  match data with
  | .obj _ =>
      let dataPath := fieldPath path "data"
      match tag with
      | "turn/start" => do
          rejectSurfaceMetadata event path
          return .turnStart (← decodeRequiredNat data dataPath "turn")
      | "turn/end" => do
          rejectSurfaceMetadata event path
          let turn ← decodeRequiredNat data dataPath "turn"
          let reason ← decodeTurnEndReason (fieldPath dataPath "reason")
            (← requireField data dataPath "reason")
          return .turnEnd turn reason
      | "step/start" => do
          rejectSurfaceMetadata event path
          return .stepStart
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
      | "step/end" => do
          rejectSurfaceMetadata event path
          return .stepEnd
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
      | "tool/call" => do
          rejectSurfaceMetadata event path
          return .toolCall
            (← decodeRequiredNat data dataPath "turn")
            (← decodeRequiredNat data dataPath "step")
            (← decodeRequiredString data dataPath "callId")
            (← decodeRequiredString data dataPath "name")
            (← decodeRequiredString data dataPath "arguments")
      | "tool/result" =>
          .toolResult <$> decodeToolResultData event path data dataPath
      | tag => .error (.unsupportedTag (fieldPath path "type") tag)
  | json => .error (.typeMismatch (fieldPath path "data") "object" (jsonKind json))

private def decodeEventAt (path : List PathSegment) : Lean.Json → Except DecodeError WireEvent
  | event@(.obj _) => do
      rejectPresent event path "ignorable"
      let tag ← decodeRequiredString event path "type"
      let seq ← decodeRequiredNat event path "seq"
      let time ← decodeRequiredNat event path "time"
      let data ← requireField event path "data"
      let payload ← decodePayload event path tag data
      .ok { seq, time, payload }
  | json => .error (.typeMismatch path "object" (jsonKind json))

/-- Decode one current upstream session-event JSON AST in the supported subset. -/
def decodeEvent (json : Lean.Json) : Except DecodeError WireEvent :=
  decodeEventAt [] json

private def decodeEventsAt : Nat → List Lean.Json → Except DecodeError (List WireEvent)
  | _, [] => .ok []
  | index, json :: rest => do
      let event ← decodeEventAt [.index index] json
      let events ← decodeEventsAt (index + 1) rest
      .ok (event :: events)

/-- Decode a current upstream JSON-AST event list with element-aware paths. -/
def decodeEvents (json : List Lean.Json) : Except DecodeError (List WireEvent) :=
  decodeEventsAt 0 json

/-! ## Prefix-derived call identity and state -/

/-- One current provider string id paired with its deterministic local numeric id. -/
structure CallBinding where
  providerId : String
  localId : CallId
  deriving DecidableEq, Repr

/-- Call-id assignment state with freshness facts exposed to later refinements. -/
structure BindingState where
  nextLocalId : Nat
  bindings : List CallBinding
  providerNodup : (bindings.map CallBinding.providerId).Nodup
  localNodup : (bindings.map CallBinding.localId).Nodup
  localBelowNext : ∀ binding ∈ bindings, binding.localId.value < nextLocalId

namespace BindingState

def empty : BindingState where
  nextLocalId := 0
  bindings := []
  providerNodup := by simp
  localNodup := by simp
  localBelowNext := by simp

def clear (state : BindingState) : BindingState where
  nextLocalId := state.nextLocalId
  bindings := []
  providerNodup := by simp
  localNodup := by simp
  localBelowNext := by simp

def findProvider (providerId : String) : List CallBinding → Option CallBinding
  | [] => none
  | binding :: rest =>
      if binding.providerId = providerId then some binding else findProvider providerId rest

end BindingState

/-- Refiner state advanced only by jointly successful Session and Protocol validation. -/
structure State where
  session : Session.Session Session.noExtensions
  protocol : SessionState
  calls : BindingState

namespace State

/-- Current Harness turn numbering starts at one; local step normalization starts at zero. -/
def initial : State where
  session := Session.Session.empty Session.noExtensions
  protocol := .ready 1
  calls := .empty

end State

/-- Stateful failures distinguish translation, session, and protocol rejection. -/
inductive RefinementError where
  | zeroStep
  | duplicateProviderCall (providerId : String)
  | unknownProviderCall (providerId : String)
  | mismatchedToolResultIds (sourceId blockId : String)
  | cannotDeriveTurnEndStep (state : RuntimeState)
  | session (error : Session.ValidationError)
  | protocol (error : Cordis.ValidationError)
  deriving DecidableEq, Repr

private def normalizeStep (step : SafeNat) : Except RefinementError Nat :=
  match step.value with
  | 0 => .error .zeroStep
  | localStepValue + 1 => .ok localStepValue

private structure Allocation (before : BindingState) (providerId : String) where
  localId : CallId
  after : BindingState

private def allocate (before : BindingState) (providerId : String) :
    Except RefinementError (Allocation before providerId) :=
  if freshProvider : providerId ∉ before.bindings.map CallBinding.providerId then
    let localId : CallId := { value := before.nextLocalId }
    have freshLocal : localId ∉ before.bindings.map CallBinding.localId := by
      intro member
      rcases List.mem_map.mp member with ⟨binding, bindingMember, bindingEq⟩
      have below := before.localBelowNext binding bindingMember
      have equalValue := congrArg CallId.value bindingEq
      exact (Nat.ne_of_lt below) equalValue
    let binding : CallBinding := { providerId, localId }
    .ok {
      localId
      after := {
        nextLocalId := before.nextLocalId + 1
        bindings := binding :: before.bindings
        providerNodup := List.nodup_cons.mpr ⟨freshProvider, before.providerNodup⟩
        localNodup := List.nodup_cons.mpr ⟨freshLocal, before.localNodup⟩
        localBelowNext := by
          intro current member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact Nat.lt_succ_self before.nextLocalId
          · exact Nat.lt_succ_of_lt (before.localBelowNext current member)
      }
    }
  else
    .error (.duplicateProviderCall providerId)

/-! ## Joint local candidates and proof-producing refinement -/

/-- Exact local event, protocol projection, and next call map proposed for one wire event. -/
structure Candidate (before : State) (wire : WireEvent) where
  localEvent : Session.LoggedEvent Session.noExtensions
  runtime : RuntimeEvent
  calls : BindingState
  seq_eq : localEvent.seq = wire.seq.value
  projection_eq : Session.LoggedEvent.protocolEvent? localEvent = some runtime

private def logOnlyEvent (seq : Nat) (kind : Session.Kind Session.noExtensions .logOnly)
    (payload : kind.Payload) : Session.LoggedEvent Session.noExtensions where
  visibility := .logOnly
  seq
  kind
  payload
  intent := .token

private def toolResultEvent (seq : Nat) (payload : Session.ToolResultPayload)
    (sources : List Nat) : Session.LoggedEvent Session.noExtensions where
  visibility := .surface
  seq
  kind := .toolResult
  payload
  intent := .append sources

private def candidate (before : State) (wire : WireEvent) :
    Except RefinementError (Candidate before wire) :=
  match wire.payload with
  | .turnStart turn =>
      let localEvent := logOnlyEvent wire.seq.value .turnStart { turn := turn.value }
      .ok {
        localEvent
        runtime := .turnStart turn.value
        calls := before.calls
        seq_eq := rfl
        projection_eq := rfl
      }
  | .turnEnd turn reason =>
      match before.protocol with
      | .turn _ nextStep =>
          let localEvent := logOnlyEvent wire.seq.value .turnEnd {
            turn := turn.value, nextStep, reason := reason.toLocal
          }
          .ok {
            localEvent
            runtime := .turnEnd turn.value nextStep
            calls := before.calls.clear
            seq_eq := rfl
            projection_eq := rfl
          }
      | protocol => .error (.cannotDeriveTurnEndStep (eraseState protocol))
  | .stepStart turn step => do
      let localStep ← normalizeStep step
      let localEvent := logOnlyEvent wire.seq.value .stepStart {
        turn := turn.value, step := localStep
      }
      .ok {
        localEvent
        runtime := .stepStart turn.value localStep
        calls := before.calls
        seq_eq := rfl
        projection_eq := rfl
      }
  | .stepEnd turn step => do
      let localStep ← normalizeStep step
      let localEvent := logOnlyEvent wire.seq.value .stepEnd {
        turn := turn.value, step := localStep
      }
      .ok {
        localEvent
        runtime := .stepEnd turn.value localStep
        calls := before.calls.clear
        seq_eq := rfl
        projection_eq := rfl
      }
  | .toolCall turn step providerId name arguments => do
      let localStep ← normalizeStep step
      let allocated ← allocate before.calls providerId
      let localEvent := logOnlyEvent wire.seq.value .toolCall {
        turn := turn.value
        step := localStep
        call := { id := allocated.localId, name, arguments }
      }
      .ok {
        localEvent
        runtime := .toolCall turn.value localStep allocated.localId
        calls := allocated.after
        seq_eq := rfl
        projection_eq := rfl
      }
  | .toolResult result => do
      if _same : result.sourceCallId = result.blockCallId then
        let binding ← match
            BindingState.findProvider result.sourceCallId before.calls.bindings with
          | some binding => .ok binding
          | none => .error (.unknownProviderCall result.sourceCallId)
        let localStep ← normalizeStep result.step
        let sources := result.sourceEventSeqs.map (·.value)
        let localEvent := toolResultEvent wire.seq.value {
          turn := result.turn.value
          step := localStep
          callId := binding.localId
          content := result.content
          isError := result.isError
        } sources
        .ok {
          localEvent
          runtime := .toolResult result.turn.value localStep binding.localId
          calls := before.calls
          seq_eq := rfl
          projection_eq := rfl
        }
      else
        .error (.mismatchedToolResultIds result.sourceCallId result.blockCallId)

/-- One wire event admitted by both local validators with exact structural projection. -/
structure RefinedEvent (before : State) (wire : WireEvent) where
  candidate : Candidate before wire
  append : Session.ValidatedAppend before.session candidate.localEvent
  protocol : Cordis.ValidatedEvent before.protocol candidate.runtime

namespace RefinedEvent

def after {before : State} {wire : WireEvent} (event : RefinedEvent before wire) : State where
  session := event.append.apply
  protocol := event.protocol.finish
  calls := event.candidate.calls

/-- The appended local event projects to the exact raw protocol event that was validated. -/
theorem projection_exact {before : State} {wire : WireEvent}
    (event : RefinedEvent before wire) :
    Session.LoggedEvent.protocolEvent? event.candidate.localEvent =
      some event.candidate.runtime :=
  event.candidate.projection_eq

/-- Physical local sequence identity is preserved exactly from the upstream envelope. -/
theorem seq_exact {before : State} {wire : WireEvent} (event : RefinedEvent before wire) :
    event.candidate.localEvent.seq = wire.seq.value :=
  event.candidate.seq_eq

/-- One accepted event extends the physical local log by exactly its translated event. -/
theorem events_eq {before : State} {wire : WireEvent} (event : RefinedEvent before wire) :
    event.after.session.events = before.session.events ++ [event.candidate.localEvent] :=
  event.append.apply_events

/-- One accepted append extends the local structural projection by its exact raw event. -/
theorem protocolProjection_eq {before : State} {wire : WireEvent}
    (event : RefinedEvent before wire) :
    Session.protocolProjection event.after.session.events =
      Session.protocolProjection before.session.events ++ [event.candidate.runtime] := by
  rw [event.events_eq]
  simp only [Session.protocolProjection, List.filterMap_append]
  have singleton :
      List.filterMap Session.LoggedEvent.protocolEvent? [event.candidate.localEvent] =
        [event.candidate.runtime] := by
    simp only [List.filterMap]
    rw [event.projection_exact]
  rw [singleton]

end RefinedEvent

/-- Translate and jointly validate one source-shaped wire event. -/
def refineEvent (before : State) (wire : WireEvent) :
    Except RefinementError (RefinedEvent before wire) := do
  let translated ← candidate before wire
  let append ← match Session.validateAppend before.session translated.localEvent with
    | .ok validated => .ok validated
    | .error error => .error (.session error)
  let protocol ← match Cordis.validateEvent before.protocol translated.runtime with
    | .ok validated => .ok validated
    | .error error => .error (.protocol error)
  .ok { candidate := translated, append, protocol }

/-- A sequential certificate chaining every jointly validated event. -/
inductive ValidatedSequence : State → List WireEvent → State → Type where
  | nil (state : State) : ValidatedSequence state [] state
  | cons {seed : State} {event : WireEvent} {rest : List WireEvent} {final : State}
      (head : RefinedEvent seed event)
      (tail : ValidatedSequence head.after rest final) :
      ValidatedSequence seed (event :: rest) final

namespace ValidatedSequence

/-- The intrinsic protocol trace obtained by composing each per-event witness. -/
def protocolTrace {seed final : State} {events : List WireEvent} :
    ValidatedSequence seed events final → Cordis.Trace seed.protocol final.protocol
  | .nil _ => .nil
  | .cons head tail => .cons head.protocol.event tail.protocolTrace

/-- Runtime protocol erasure is exactly the per-event projection sequence. -/
def runtimeEvents {seed final : State} {events : List WireEvent} :
    ValidatedSequence seed events final → List RuntimeEvent
  | .nil _ => []
  | .cons head tail => head.candidate.runtime :: tail.runtimeEvents

theorem protocolTrace_erase {seed final : State} {events : List WireEvent}
    (sequence : ValidatedSequence seed events final) :
    sequence.protocolTrace.erase = sequence.runtimeEvents := by
  induction sequence with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change head.protocol.event.erase :: tail.protocolTrace.erase =
        head.candidate.runtime :: tail.runtimeEvents
      rw [head.protocol.erase_eq]
      exact congrArg (List.cons head.candidate.runtime) inductionHypothesis

/-- The final local session projection is the seed projection followed by every refined event. -/
theorem sessionProjection_eq {seed final : State} {events : List WireEvent}
    (sequence : ValidatedSequence seed events final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection seed.session.events ++ sequence.runtimeEvents := by
  induction sequence with
  | nil => simp [runtimeEvents]
  | cons head tail inductionHypothesis =>
      rw [inductionHypothesis, head.protocolProjection_eq]
      simp [runtimeEvents, List.append_assoc]

end ValidatedSequence

/-- Validate a decoded wire sequence from left to right. -/
def validateSequence : (seed : State) → (events : List WireEvent) →
    Except RefinementError (Σ final, ValidatedSequence seed events final)
  | seed, [] => .ok ⟨seed, .nil seed⟩
  | seed, event :: rest => do
      let head ← refineEvent seed event
      let ⟨final, tail⟩ ← validateSequence head.after rest
      .ok ⟨final, .cons head tail⟩

/-- JSON input, exact decoded wire events, and their sequential joint certificate. -/
structure ValidatedJsonLog (input : List Lean.Json) where
  events : List WireEvent
  decode_eq : decodeEvents input = .ok events
  final : State
  sequence : ValidatedSequence State.initial events final

namespace ValidatedJsonLog

/-- The complete local protocol projection is exactly the intrinsic trace erasure. -/
theorem projection_exact {input : List Lean.Json} (validated : ValidatedJsonLog input) :
    Session.protocolProjection validated.final.session.events =
      validated.sequence.protocolTrace.erase := by
  rw [validated.sequence.sessionProjection_eq]
  simp [State.initial, Session.Session.empty, Session.protocolProjection]
  exact validated.sequence.protocolTrace_erase.symm

end ValidatedJsonLog

/-- Decode and jointly validate a finite supported current-Harness event prefix. -/
def validateJsonLog (input : List Lean.Json) :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) :=
  match decoded : decodeEvents input with
  | .error error => .error (.inl error)
  | .ok events =>
      match validateSequence State.initial events with
      | .error error => .error (.inr error)
      | .ok ⟨final, sequence⟩ => .ok { events, decode_eq := decoded, final, sequence }

/-! ## Executable current-shape example and rejection witnesses -/

def exampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 100),
    ("data", Lean.Json.mkObj [("turn", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "step/start"), ("seq", .num 1), ("time", .num 101),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/call"), ("seq", .num 2), ("time", .num 102),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1), ("callId", .str "provider-call"),
      ("name", .str "lookup"), ("arguments", .str "{\"q\":\"lean\"}")
    ])
  ],
  Lean.Json.mkObj [
    ("type", .str "tool/result"), ("seq", .num 3), ("time", .num 103),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("step", .num 1),
      ("message", Lean.Json.mkObj [
        ("source", Lean.Json.mkObj [
          ("kind", .str "tool"), ("callId", .str "provider-call")
        ]),
        ("content", .arr #[Lean.Json.mkObj [
          ("type", .str "tool-result"), ("toolCallId", .str "provider-call"),
          ("content", .arr #[Lean.Json.mkObj [
            ("type", .str "text"), ("text", .str "result")
          ]]),
          ("isError", .bool false)
        ]]),
        ("role", .str "user"), ("id", .str "message-1")
      ])
    ]),
    ("sourceEventSeqs", .arr #[.num 2]), ("surfaceOp", .str "append")
  ],
  Lean.Json.mkObj [
    ("type", .str "step/end"), ("seq", .num 4), ("time", .num 104),
    ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)])
  ],
  Lean.Json.mkObj [
    ("type", .str "turn/end"), ("seq", .num 5), ("time", .num 105),
    ("data", Lean.Json.mkObj [
      ("turn", .num 1), ("reason", Lean.Json.mkObj [("kind", .str "completed")])
    ])
  ]
]

/-- Proof-erased observation used only to state executable example outcomes compactly. -/
structure ValidationSummary where
  protocol : SessionState
  nextSeq : Nat
  messages : List Session.Message
  runtimeEvents : List RuntimeEvent
  deriving DecidableEq

/-- Observe a successful certificate without replacing the proof-producing return type. -/
def validationSummary {input : List Lean.Json} :
    Except (DecodeError ⊕ RefinementError) (ValidatedJsonLog input) → Option ValidationSummary
  | .error _ => none
  | .ok validated => some {
      protocol := validated.final.protocol
      nextSeq := validated.final.session.nextSeq
      messages := validated.final.session.messages
      runtimeEvents := validated.sequence.runtimeEvents
    }

/-- Full supported JSON prefix reaches a closed local turn and one tool-result surface node. -/
theorem validate_example :
    validationSummary (validateJsonLog exampleJson) = some {
      protocol := .ready 2
      nextSeq := 6
      messages := [.toolResult { value := 0 } "result" false]
      runtimeEvents := [
        .turnStart 1,
        .stepStart 1 0,
        .toolCall 1 0 { value := 0 },
        .toolResult 1 0 { value := 0 },
        .stepEnd 1 0,
        .turnEnd 1 1
      ]
    } := by
  rfl

/-- Local `nextStep = 1` at turn end is derived from the preceding certified step transition. -/
theorem example_turnEndStep_isDerived :
    (validationSummary (validateJsonLog exampleJson)).map
      (fun summary => summary.runtimeEvents.getLast?) = some (some (.turnEnd 1 1)) := by
  rfl

/-- Current assistant message payloads are explicitly outside this supported subset. -/
theorem reject_assistantMessage :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "assistant/message"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [])
    ]) = .error (.unsupportedTag [.field "type"] "assistant/message") :=
  rfl

/-- Log-only boundary events cannot smuggle conditional surface metadata into the local log. -/
theorem reject_surfaceMetadataOnStepStart :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "step/start"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [("turn", .num 1), ("step", .num 1)]),
      ("surfaceOp", .str "append")
    ]) = .error (.unsupportedField [] "surfaceOp") :=
  rfl

/-- Core events marked skippable are rejected because local reconstruction cannot preserve it. -/
theorem reject_ignorableCoreEvent :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "turn/start"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [("turn", .num 1)]),
      ("ignorable", .bool true)
    ]) = .error (.unsupportedField [] "ignorable") :=
  rfl

/-- An upstream abort cause has more structure than the local supported reason subset. -/
theorem reject_unmodeledTurnEndReason :
    decodeEvent (Lean.Json.mkObj [
      ("type", .str "turn/end"), ("seq", .num 0), ("time", .num 0),
      ("data", Lean.Json.mkObj [
        ("turn", .num 1),
        ("reason", Lean.Json.mkObj [
          ("kind", .str "aborted"),
          ("reason", Lean.Json.mkObj [("kind", .str "user")])
        ])
      ])
    ]) = .error (.unsupportedTag
      [.field "data", .field "reason", .field "kind"] "aborted") :=
  rfl

/-- An upstream zero step has no predecessor under the named one-to-zero normalization. -/
theorem reject_zeroStep :
    let event : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .stepStart { value := 1, safe := by decide }
        { value := 0, safe := by decide }
    }
    refineEvent State.initial event = .error .zeroStep := by
  rfl

/-- A tool result whose nested source and block ids disagree is never assigned a local id. -/
theorem reject_mismatchedToolResultIds :
    let result : WireToolResult := {
      turn := { value := 1, safe := by decide }
      step := { value := 1, safe := by decide }
      messageId := "m"
      sourceCallId := "source"
      blockCallId := "block"
      content := "result"
      isError := false
      sourceEventSeqs := []
    }
    let wire : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .toolResult result
    }
    refineEvent State.initial wire =
      .error (.mismatchedToolResultIds "source" "block") := by
  rfl

/-- A turn-end next-step value cannot be invented when the validated prefix is not in a turn. -/
theorem reject_underdeterminedTurnEnd :
    let wire : WireEvent := {
      seq := { value := 0, safe := by decide }
      time := { value := 0, safe := by decide }
      payload := .turnEnd { value := 1, safe := by decide } .completed
    }
    refineEvent State.initial wire =
      .error (.cannotDeriveTurnEndStep (.ready 1)) := by
  rfl

end Cordis.SessionRefinement
