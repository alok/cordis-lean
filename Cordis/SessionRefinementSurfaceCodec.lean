import Cordis.SessionRefinementTextCodec

/-!
# Canonical surface and tool-result codec

`SessionRefinement` already decodes the current source-shaped `user/message` and `tool/result`
records, but the smaller scalar codec intentionally left those payloads one-way.  This module
closes that gap for the text-user and single-text-tool-result subset used by the local Harness
fixtures.  The encoder emits the exact outer metadata required by the decoder, preserves the
typed safe-integer witnesses, and retains `isError` as data rather than translating it to a local
success flag.

Assistant surface messages, image blocks, request metadata, and provider/tool-owned opaque
fields remain fail-closed.  A successful AST round trip is proved, then composed with the existing
JSONL parser and UTF-8 renderer.  This is a source-shaped local codec, not a claim of deployed
logger compatibility, provider obedience, or complete future event-union coverage.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement.SurfaceCodec

open Cordis
open Cordis.SessionRefinement

inductive EncodeError where
  | unsupportedPayload (tag : String)
  | unsupportedMessage (tag : String)
  deriving DecidableEq, Repr

def rawObj (fields : List (String × Lean.Json)) : Lean.Json :=
  .obj (Std.TreeMap.Raw.ofList fields compare)

def safeNatJson (value : SafeNat) : Lean.Json :=
  .num (Lean.JsonNumber.fromNat value.value)

def sourceEventSeqsFields (values : Option (List SafeNat)) :
    List (String × Lean.Json) :=
  match values with
  | none => []
  | some seqs => [("sourceEventSeqs", .arr (seqs.map safeNatJson).toArray)]

def surfaceOpJson : WireSurfaceOp → Lean.Json
  | .append => .str "append"
  | .replace start endSeq =>
      rawObj [("op", .str "replace"), ("start", safeNatJson start),
        ("end", safeNatJson endSeq)]

def surfaceFields (sourceEventSeqs : Option (List SafeNat))
    (surfaceOp : WireSurfaceOp) : List (String × Lean.Json) :=
  ("surfaceOp", surfaceOpJson surfaceOp) :: sourceEventSeqsFields sourceEventSeqs

def eventObj (seq time : SafeNat) (tag : String) (data : Lean.Json)
    (extra : List (String × Lean.Json)) : Lean.Json :=
  rawObj (("type", .str tag) :: ("seq", safeNatJson seq) ::
    ("time", safeNatJson time) :: ("data", data) :: extra)

def textBlockJson (block : WireTextBlock) : Lean.Json :=
  rawObj [("type", .str "text"), ("text", .str block.text)]

def textBlocksJson (blocks : List WireTextBlock) : Lean.Json :=
  .arr (blocks.map textBlockJson).toArray

def userMessageJson (message : WireUserMessage) : Lean.Json :=
  rawObj [("id", .str message.id), ("role", .str "user"),
    ("source", rawObj [("kind", .str "user")]),
    ("content", textBlocksJson message.content)]

def userEventJson (seq time : SafeNat) (append : WireSurfaceAppend) : Lean.Json :=
  match append.message with
  | .user message =>
      eventObj seq time "user/message" (userMessageJson message)
        (surfaceFields append.sourceEventSeqs append.surfaceOp)
  | .assistant _ => Lean.Json.null

def toolResultMessageJson (result : WireToolResult) : Lean.Json :=
  rawObj [("source", rawObj [("kind", .str "tool"),
      ("callId", .str result.sourceCallId)]),
    ("content", .arr #[rawObj [
      ("type", .str "tool-result"), ("toolCallId", .str result.blockCallId),
      ("content", .arr #[rawObj [("type", .str "text"),
        ("text", .str result.content)]]), ("isError", .bool result.isError)]]),
    ("role", .str "user"), ("id", .str result.messageId)]

/-! The event sequence and timestamp for a tool result are not stored in `WireToolResult`.
The public encoder therefore takes them explicitly rather than guessing from provenance. -/

def toolResultEvent (seq time : SafeNat) (result : WireToolResult) : Lean.Json :=
  eventObj seq time "tool/result"
    (rawObj [("turn", safeNatJson result.turn), ("step", safeNatJson result.step),
      ("message", toolResultMessageJson result)])
    (surfaceFields (some result.sourceEventSeqs) result.surfaceOp)

def encodeUserMessage (seq time : SafeNat) (append : WireSurfaceAppend) :
    Except EncodeError Lean.Json :=
  match append.message with
  | .user _ => .ok (userEventJson seq time append)
  | .assistant _ => .error (.unsupportedMessage "assistant/message")

def encodeToolResult (seq time : SafeNat) (result : WireToolResult) :
    Except EncodeError Lean.Json :=
  .ok (toolResultEvent seq time result)

def scalarError : Cordis.SessionRefinement.Codec.EncodeError → EncodeError
  | .unsupportedPayload tag => .unsupportedPayload tag

def encodeWireEvent (event : WireEvent) : Except EncodeError Lean.Json :=
  match event.payload with
  | .userMessage append => encodeUserMessage event.seq event.time append
  | .toolResult result => encodeToolResult event.seq event.time result
  | .assistantMessage _ _ _ => .error (.unsupportedPayload "assistant/message")
  | _ =>
      (Cordis.SessionRefinement.Codec.encodeWireEvent event).mapError scalarError

private theorem rawField {fields : List (String × Lean.Json)} {name : String}
    {value : Lean.Json} (distinct : List.Pairwise (fun a b =>
      ¬compare a.1 b.1 = Ordering.eq) fields) (mem : (name, value) ∈ fields) :
    field? (.obj (Std.TreeMap.Raw.ofList fields compare)) name = some value := by
  exact objectField_raw_mem distinct mem

private theorem textBlock_decode (path : List PathSegment) (block : WireTextBlock) :
    decodeTextBlock path (textBlockJson block) = .ok block.text := by
  have typeField : field? (.obj (Std.TreeMap.Raw.ofList [("type", .str "text"),
      ("text", .str block.text)] compare)) "type" = some (.str "text") := by
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  have textField : field? (.obj (Std.TreeMap.Raw.ofList [("type", .str "text"),
      ("text", .str block.text)] compare)) "text" = some (.str block.text) := by
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  unfold decodeTextBlock
  simp only [textBlockJson, rawObj]
  simp only [decodeRequiredString, requireField]
  rw [typeField, textField]
  rfl

private theorem textBlocks_loop_decode (path : List PathSegment) (start : Nat)
    (blocks : List WireTextBlock) :
    decodeTextBlocks.loop path start (blocks.map textBlockJson) = .ok blocks := by
  induction blocks generalizing start with
  | nil => rfl
  | cons head tail ih =>
      simp [decodeTextBlocks.loop, textBlock_decode, ih]
      rfl

private theorem textBlocks_decode (path : List PathSegment) (blocks : List WireTextBlock) :
    decodeTextBlocks path (textBlocksJson blocks) = .ok blocks := by
  change decodeTextBlocks.loop path 0 (blocks.map textBlockJson) = .ok blocks
  exact textBlocks_loop_decode path 0 blocks

private theorem safeNatList_loop_decode (path : List PathSegment) (start : Nat)
    (values : List SafeNat) :
    decodeSafeNatList.loop path start (values.map safeNatJson) = .ok values := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail ih =>
      have headDecoded : decodeSafeNat (indexPath path start) (safeNatJson head) = .ok head := by
        change decodeSafeNat (indexPath path start) (Canonical.safeNatJson head) = .ok head
        exact Canonical.decodeSafeNat_safeNat (indexPath path start) head
      simp [decodeSafeNatList.loop, headDecoded, ih]
      rfl

private theorem safeNatList_decode (path : List PathSegment) (values : List SafeNat) :
    decodeSafeNatList path (.arr (values.map safeNatJson).toArray) = .ok values := by
  change decodeSafeNatList.loop path 0 (values.map safeNatJson) = .ok values
  exact safeNatList_loop_decode path 0 values

private theorem safeNat_decode (path : List PathSegment) (value : SafeNat) :
    decodeSafeNat path (safeNatJson value) = .ok value := by
  change decodeSafeNat path (Canonical.safeNatJson value) = .ok value
  exact Canonical.decodeSafeNat_safeNat path value

private theorem userMessage_decode (path : List PathSegment) (message : WireUserMessage) :
    decodeUserMessage path (userMessageJson message) = .ok message := by
  have idField : field? (userMessageJson message) "id" = some (.str message.id) := by
    unfold userMessageJson rawObj
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  have roleField : field? (userMessageJson message) "role" = some (.str "user") := by
    unfold userMessageJson rawObj
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  have sourceField : field? (userMessageJson message) "source" =
      some (rawObj [("kind", .str "user")]) := by
    unfold userMessageJson rawObj
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  have sourceKind : field?
      (.obj (Std.TreeMap.Raw.ofList [("kind", .str "user")] compare)) "kind" =
      some (.str "user") := by
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  have contentField : field? (userMessageJson message) "content" =
      some (textBlocksJson message.content) := by
    unfold userMessageJson rawObj
    apply rawField
    · simp [List.pairwise_cons]
    · simp
  unfold decodeUserMessage
  simp_all (maxSteps := 1000000) [Bind.bind, Except.bind, decodeRequiredString,
    decodeString, requireField, decodeTextBlocks, field?, fieldPath, rawObj,
    textBlocksJson, textBlocks_loop_decode] <;> rfl

private def resultExample : WireToolResult := {
  turn := { value := 1, safe := by decide }
  step := { value := 1, safe := by decide }
  messageId := "message-1"
  sourceCallId := "call-1"
  blockCallId := "call-1"
  content := "unavailable"
  isError := true
  sourceEventSeqs := [{ value := 4, safe := by decide }]
  surfaceOp := .append
}

example : decodeEvent (toolResultEvent
    { value := 5, safe := by decide } { value := 105, safe := by decide } resultExample) = .ok {
    seq := { value := 5, safe := by decide }
    time := { value := 105, safe := by decide }
    payload := .toolResult resultExample } := by
  simp only [toolResultEvent, eventObj, toolResultMessageJson, rawObj,
    surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
  unfold Cordis.SessionRefinement.decodeEventAt
  simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
    Cordis.SessionRefinement.decodePayload,
    Cordis.SessionRefinement.decodeToolResultData,
    Cordis.SessionRefinement.decodeToolResultBlock,
    Cordis.SessionRefinement.decodeSurfaceMetadata,
    Cordis.SessionRefinement.decodeTextBlock,
    Cordis.SessionRefinement.decodeRequiredString,
    Cordis.SessionRefinement.decodeRequiredNat,
    Cordis.SessionRefinement.decodeOptionalBool,
    Cordis.SessionRefinement.decodeBool,
    Cordis.SessionRefinement.decodeSingleton,
    Cordis.SessionRefinement.requireField,
    Cordis.SessionRefinement.rejectPresent,
    Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
    Cordis.SessionRefinement.decodeString, safeNat_decode, safeNatList_decode] <;> rfl

theorem decode_toolResult (seq time : SafeNat) (result : WireToolResult) :
    decodeEvent (toolResultEvent seq time result) = .ok {
      seq, time, payload := .toolResult result } := by
  cases result with
  | mk turn step messageId sourceCallId blockCallId content isError sourceEventSeqs surfaceOp =>
      cases surfaceOp with
      | append =>
          simp only [toolResultEvent, eventObj, toolResultMessageJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeToolResultData,
            Cordis.SessionRefinement.decodeToolResultBlock,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlock,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.decodeOptionalBool,
            Cordis.SessionRefinement.decodeSingleton,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString, safeNat_decode, safeNatList_decode] <;> rfl
      | replace start endSeq =>
          simp only [toolResultEvent, eventObj, toolResultMessageJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeToolResultData,
            Cordis.SessionRefinement.decodeToolResultBlock,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlock,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.decodeOptionalBool,
            Cordis.SessionRefinement.decodeSingleton,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString, safeNat_decode, safeNatList_decode] <;> rfl

theorem decode_userMessage (seq time : SafeNat) (message : WireUserMessage)
    (sourceEventSeqs : Option (List SafeNat)) (surfaceOp : WireSurfaceOp) :
    decodeEvent (userEventJson seq time {
      message := .user message, sourceEventSeqs, surfaceOp }) = .ok {
        seq, time, payload := .userMessage {
          message := .user message, sourceEventSeqs, surfaceOp } } := by
  cases surfaceOp with
  | append =>
      cases sourceEventSeqs with
      | none =>
          simp only [userEventJson, eventObj, userMessageJson, textBlocksJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeUserMessageData,
            Cordis.SessionRefinement.decodeUserMessage,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlocks,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString,
            textBlocks_loop_decode, safeNat_decode] <;> rfl
      | some sourceEventSeqs =>
          simp only [userEventJson, eventObj, userMessageJson, textBlocksJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeUserMessageData,
            Cordis.SessionRefinement.decodeUserMessage,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlocks,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString,
            textBlocks_loop_decode, safeNat_decode,
            safeNatList_decode] <;> rfl
  | replace start endSeq =>
      cases sourceEventSeqs with
      | none =>
          simp only [userEventJson, eventObj, userMessageJson, textBlocksJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeUserMessageData,
            Cordis.SessionRefinement.decodeUserMessage,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlocks,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString,
            textBlocks_loop_decode, safeNat_decode] <;> rfl
      | some sourceEventSeqs =>
          simp only [userEventJson, eventObj, userMessageJson, textBlocksJson, rawObj,
            surfaceFields, surfaceOpJson, sourceEventSeqsFields, decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeUserMessageData,
            Cordis.SessionRefinement.decodeUserMessage,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeTextBlocks,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString,
            textBlocks_loop_decode, safeNat_decode,
            safeNatList_decode] <;> rfl

end Cordis.SessionRefinement.SurfaceCodec
