import Cordis.SessionRefinementTextCodec

/-!
# Canonical surface and tool-result codec

`SessionRefinement` already decodes the current source-shaped `user/message` and `tool/result`
records, but the smaller scalar codec intentionally left those payloads one-way.  This module
closes that gap for the text-user, assistant-surface, and single-text-tool-result subset used by
the local Harness fixtures.  The encoder emits the exact outer metadata required by the decoder,
preserves typed safe-integer witnesses, and retains `isError` as data rather than translating it to
a local success flag.

Assistant text/reasoning, tagged raw image, and complete tool-call surface messages are now
encoded as well as decoded.  Image schema semantics, request metadata, and provider/tool-owned
opaque fields remain external or fail-closed; source-event references and replacement operations
are emitted from their typed metadata.  A
successful AST round trip is proved, then composed with the
existing JSONL parser and UTF-8 renderer.  This is a source-shaped local codec, not a claim of
deployed logger compatibility, provider obedience, or complete future event-union coverage.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement.SurfaceCodec

open Cordis
open Cordis.SessionRefinement

inductive EncodeError where
  | unsupportedPayload (tag : String)
  | unsupportedMessage (tag : String)
  | unsupportedAssistantBlock (tag : String)
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

def imageBlockJson (raw : Lean.Json) : Except EncodeError Lean.Json :=
  match raw with
  | .obj _ =>
      match field? raw "type" with
      | some (.str "image") => .ok raw
      | _ => .error (.unsupportedAssistantBlock "image")
  | _ => .error (.unsupportedAssistantBlock "image")

def assistantBlockJson : WireAssistantBlock → Except EncodeError Lean.Json
  | .text text => .ok (rawObj [("type", .str "text"), ("text", .str text)])
  | .reasoning text => .ok (rawObj [("type", .str "reasoning"), ("text", .str text)])
  | .image raw => imageBlockJson raw
  | .toolCall providerId name arguments =>
      .ok (rawObj [("type", .str "tool-call"), ("id", .str providerId),
        ("name", .str name), ("arguments", .str arguments)])

def assistantBlocksJson (blocks : List WireAssistantBlock) :
    Except EncodeError Lean.Json := do
  let encoded ← blocks.mapM assistantBlockJson
  .ok (.arr encoded.toArray)

def wireUsageJson (usage : WireUsage) : Lean.Json :=
  rawObj ([("inputTokens", safeNatJson usage.inputTokens),
    ("outputTokens", safeNatJson usage.outputTokens)] ++
    (match usage.cacheReadTokens with
    | none => []
    | some value => [("cacheReadTokens", safeNatJson value)]) ++
    (match usage.cacheWriteTokens with
    | none => []
    | some value => [("cacheWriteTokens", safeNatJson value)]) ++
    (match usage.reasoningTokens with
    | none => []
    | some value => [("reasoningTokens", safeNatJson value)]))

def wireUsageFields (usage : Option WireUsage) : List (String × Lean.Json) :=
  match usage with
  | none => []
  | some value => [("usage", wireUsageJson value)]

def assistantSourceJson (message : WireAssistantMessage) : Lean.Json :=
  rawObj [("kind", .str "model"), ("provider", .str message.provider),
    ("model", .str message.model)]

def assistantMessageJson (message : WireAssistantMessage) (content : Lean.Json) : Lean.Json :=
  rawObj [("id", .str message.id), ("role", .str "assistant"),
    ("source", assistantSourceJson message), ("content", content)]

def assistantEventJsonWithMetadata (seq time turn step : SafeNat) (message : WireAssistantMessage)
    (content : Lean.Json) (sourceEventSeqs : Option (List SafeNat))
    (surfaceOp : WireSurfaceOp) : Lean.Json :=
  eventObj seq time "assistant/message"
    (rawObj ([ ("turn", safeNatJson turn), ("step", safeNatJson step),
      ("message", assistantMessageJson message content)] ++ wireUsageFields message.usage))
    (surfaceFields sourceEventSeqs surfaceOp)

def assistantEventJson (seq time turn step : SafeNat) (message : WireAssistantMessage)
    (content : Lean.Json) : Lean.Json :=
  assistantEventJsonWithMetadata seq time turn step message content none .append

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

def encodeAssistantMessage (seq time turn step : SafeNat) (append : WireSurfaceAppend) :
    Except EncodeError Lean.Json := do
  let message ← match append.message with
    | .assistant value => .ok value
    | .user _ => .error (.unsupportedMessage "user/message")
  let content ← assistantBlocksJson message.content
  .ok (assistantEventJsonWithMetadata seq time turn step message content
    append.sourceEventSeqs append.surfaceOp)

def scalarError : Cordis.SessionRefinement.Codec.EncodeError → EncodeError
  | .unsupportedPayload tag => .unsupportedPayload tag

def encodeWireEvent (event : WireEvent) : Except EncodeError Lean.Json :=
  match event.payload with
  | .userMessage append => encodeUserMessage event.seq event.time append
  | .toolResult result => encodeToolResult event.seq event.time result
  | .assistantMessage turn step append =>
      encodeAssistantMessage event.seq event.time turn step append
  | _ =>
      (Cordis.SessionRefinement.Codec.encodeWireEvent event).mapError scalarError

private theorem scalar_mapError_ok
    {result : Except Cordis.SessionRefinement.Codec.EncodeError Lean.Json}
    {json : Lean.Json} (encoded : result.mapError scalarError = .ok json) :
    result = .ok json := by
  cases result with
  | error error =>
      cases error with
      | unsupportedPayload tag => simp [Except.mapError, scalarError] at encoded
  | ok value =>
      cases encoded
      rfl

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

private theorem imageBlock_decode (path : List PathSegment) (raw : Lean.Json)
    {json : Lean.Json} (encoded : imageBlockJson raw = .ok json) :
    decodeAssistantBlock path json = .ok (.image raw) := by
  cases raw with
  | obj fields =>
      unfold imageBlockJson at encoded
      cases hType : field? (.obj fields) "type" with
      | none => simp [hType] at encoded
      | some value =>
          cases value with
          | str tag =>
              by_cases hTag : tag = "image"
              · subst tag
                rw [hType] at encoded
                cases encoded
                have hType' : objectField? (Lean.Json.obj fields) "type" =
                    some (.str "image") := by
                  simpa [field?] using hType
                simp [decodeAssistantBlock, decodeRequiredString,
                  decodeString, requireField, field?, hType'] <;> rfl
              · simp [hType, hTag] at encoded
          | num value => simp [hType] at encoded
          | bool value => simp [hType] at encoded
          | arr values => simp [hType] at encoded
          | obj nested => simp [hType] at encoded
          | null => simp [hType] at encoded
  | str value => simp [imageBlockJson] at encoded
  | num value => simp [imageBlockJson] at encoded
  | bool value => simp [imageBlockJson] at encoded
  | arr values => simp [imageBlockJson] at encoded
  | null => simp [imageBlockJson] at encoded

private theorem assistantBlock_decode (path : List PathSegment)
    (block : WireAssistantBlock) {json : Lean.Json}
    (encoded : assistantBlockJson block = .ok json) :
    decodeAssistantBlock path json = .ok block := by
  cases block with
  | text text =>
      cases encoded
      simp_all (maxSteps := 1000000) [rawObj,
        decodeAssistantBlock, decodeRequiredString, requireField, field?] <;> rfl
  | reasoning text =>
      cases encoded
      simp_all (maxSteps := 1000000) [rawObj,
        decodeAssistantBlock, decodeRequiredString, requireField, field?] <;> rfl
  | image raw =>
      exact imageBlock_decode path raw encoded
  | toolCall providerId name arguments =>
      cases encoded
      simp_all (maxSteps := 1000000) [rawObj,
        decodeAssistantBlock, decodeRequiredString, requireField, field?] <;> rfl

private theorem assistantBlocks_loop_decode
    (path : List PathSegment) (start : Nat) :
    ∀ {blocks : List WireAssistantBlock} {jsons : List Lean.Json},
      blocks.mapM assistantBlockJson = .ok jsons →
      decodeAssistantBlocks.loop path start jsons = .ok blocks := by
  intro blocks
  induction blocks generalizing start with
  | nil =>
      intro jsons encoded
      rw [List.mapM_nil] at encoded
      cases encoded
      rfl
  | cons block blocks ih =>
      intro jsons encoded
      rw [List.mapM_cons] at encoded
      cases headEncoded : assistantBlockJson block with
      | error error =>
          simp [headEncoded] at encoded
          contradiction
      | ok headJson =>
          rw [headEncoded] at encoded
          cases tailEncoded : List.mapM assistantBlockJson blocks with
          | error error =>
              simp [tailEncoded] at encoded
              contradiction
          | ok tailJsons =>
              rw [tailEncoded] at encoded
              cases encoded
              simp [decodeAssistantBlocks.loop, Bind.bind, Except.bind,
                assistantBlock_decode (indexPath path start) block headEncoded,
                ih (start + 1) tailEncoded]

private theorem assistantBlocks_decode_of_encoded
    (path : List PathSegment) (blocks : List WireAssistantBlock)
    {json : Lean.Json} (encoded : assistantBlocksJson blocks = .ok json) :
    decodeAssistantBlocks path json = .ok blocks := by
  unfold assistantBlocksJson at encoded
  cases encodedList : List.mapM assistantBlockJson blocks with
  | error error =>
      simp [encodedList] at encoded
      contradiction
  | ok jsons =>
      rw [encodedList] at encoded
      cases encoded
      change decodeAssistantBlocks.loop path 0 jsons = .ok blocks
      exact assistantBlocks_loop_decode path 0 encodedList

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

private theorem wireUsage_decode (path : List PathSegment) (usage : WireUsage) :
    decodeWireUsage path (wireUsageJson usage) = .ok usage := by
  cases usage with
  | mk inputTokens outputTokens cacheReadTokens cacheWriteTokens reasoningTokens =>
      cases cacheReadTokens <;> cases cacheWriteTokens <;> cases reasoningTokens <;>
        simp_all (maxSteps := 1000000) [Bind.bind, Except.bind, wireUsageJson, rawObj,
          decodeWireUsage, decodeRequiredNat, decodeOptionalNat, requireField, field?,
          safeNat_decode] <;> rfl

private theorem assistantMessage_decode
    (path : List PathSegment) (message : WireAssistantMessage)
    {content : Lean.Json}
    (encodedContent : assistantBlocksJson message.content = .ok content) :
    decodeAssistantMessage path (assistantMessageJson message content) = .ok {
      id := message.id
      provider := message.provider
      model := message.model
      content := message.content
      usage := none } := by
  have decodedContent := assistantBlocks_decode_of_encoded
    (fieldPath path "content") message.content encodedContent
  unfold decodeAssistantMessage
  simp_all (maxSteps := 1000000) [Bind.bind, Except.bind, assistantMessageJson,
    assistantSourceJson, rawObj, decodeRequiredString, requireField, rejectPresent,
    decodeOptionalWireUsage, field?] <;> rfl

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

theorem decode_assistantMessage
    (seq time turn step : SafeNat) (message : WireAssistantMessage)
    {content : Lean.Json}
    (encodedContent : assistantBlocksJson message.content = .ok content) :
    decodeEvent (assistantEventJson seq time turn step message content) = .ok {
      seq, time, payload := .assistantMessage turn step {
        message := .assistant message
        sourceEventSeqs := none
        surfaceOp := .append } } := by
  cases message with
  | mk id provider model blocks usage =>
      cases usage with
      | none =>
          let sourceMessage : WireAssistantMessage := {
            id := id
            provider := provider
            model := model
            content := blocks
            usage := none }
          have decodedMessage :
              decodeAssistantMessage [.field "data", .field "message"]
                (assistantMessageJson sourceMessage content) = .ok sourceMessage :=
            assistantMessage_decode [.field "data", .field "message"] sourceMessage
              encodedContent
          simp only [assistantEventJson, assistantEventJsonWithMetadata, eventObj,
            assistantMessageJson, assistantSourceJson,
            rawObj, wireUsageFields, surfaceFields, surfaceOpJson, sourceEventSeqsFields,
            decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp only [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeAssistantMessageData,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.decodeOptionalWireUsage,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString]
          have decodedMessage' := decodedMessage
          simp only [assistantMessageJson, assistantSourceJson, rawObj] at decodedMessage'
          dsimp [sourceMessage] at decodedMessage'
          simp_all (maxSteps := 1000000) [safeNat_decode]
          rfl
      | some usage =>
          let sourceMessage : WireAssistantMessage := {
            id := id
            provider := provider
            model := model
            content := blocks
            usage := none }
          have decodedMessage :
              decodeAssistantMessage [.field "data", .field "message"]
                (assistantMessageJson sourceMessage content) = .ok sourceMessage :=
            assistantMessage_decode [.field "data", .field "message"] sourceMessage
              encodedContent
          have decodedUsage :
              decodeWireUsage [.field "data", .field "usage"] (wireUsageJson usage) = .ok usage :=
            wireUsage_decode [.field "data", .field "usage"] usage
          simp only [assistantEventJson, assistantEventJsonWithMetadata, eventObj,
            assistantMessageJson, assistantSourceJson,
            rawObj, wireUsageFields, surfaceFields, surfaceOpJson, sourceEventSeqsFields,
            decodeEvent]
          unfold Cordis.SessionRefinement.decodeEventAt
          simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
            Cordis.SessionRefinement.decodePayload,
            Cordis.SessionRefinement.decodeAssistantMessageData,
            Cordis.SessionRefinement.decodeSurfaceMetadata,
            Cordis.SessionRefinement.decodeRequiredString,
            Cordis.SessionRefinement.decodeRequiredNat,
            Cordis.SessionRefinement.decodeOptionalWireUsage,
            Cordis.SessionRefinement.requireField,
            Cordis.SessionRefinement.rejectPresent,
            Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
            Cordis.SessionRefinement.decodeString]
          have decodedMessage' := decodedMessage
          simp only [assistantMessageJson, assistantSourceJson, rawObj] at decodedMessage'
          dsimp [sourceMessage] at decodedMessage'
          have decodedUsage' := decodedUsage
          simp only [wireUsageJson, rawObj] at decodedUsage'
          simp_all (maxSteps := 1000000) [wireUsageJson, rawObj, safeNat_decode]
          rfl

theorem decode_assistantMessage_withMetadata
    (seq time turn step : SafeNat) (message : WireAssistantMessage)
    (sourceEventSeqs : Option (List SafeNat)) (surfaceOp : WireSurfaceOp)
    {content : Lean.Json}
    (encodedContent : assistantBlocksJson message.content = .ok content) :
    decodeEvent (assistantEventJsonWithMetadata seq time turn step message content
      sourceEventSeqs surfaceOp) = .ok {
        seq, time, payload := .assistantMessage turn step {
          message := .assistant message
          sourceEventSeqs
          surfaceOp } } := by
  cases message with
  | mk id provider model blocks usage =>
      cases usage with
      | none =>
          let sourceMessage : WireAssistantMessage := {
            id := id
            provider := provider
            model := model
            content := blocks
            usage := none }
          have decodedMessage :
              decodeAssistantMessage [.field "data", .field "message"]
                (assistantMessageJson sourceMessage content) = .ok sourceMessage :=
            assistantMessage_decode [.field "data", .field "message"] sourceMessage
              encodedContent
          have decodedMessage' := decodedMessage
          simp only [assistantMessageJson, assistantSourceJson, rawObj] at decodedMessage'
          dsimp [sourceMessage] at decodedMessage'
          cases sourceEventSeqs <;> cases surfaceOp <;>
            simp only [assistantEventJsonWithMetadata, eventObj, assistantMessageJson,
              assistantSourceJson, rawObj, wireUsageFields, surfaceFields, surfaceOpJson,
              sourceEventSeqsFields, decodeEvent]
          all_goals
            unfold Cordis.SessionRefinement.decodeEventAt
            simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
              Cordis.SessionRefinement.decodePayload,
              Cordis.SessionRefinement.decodeAssistantMessageData,
              Cordis.SessionRefinement.decodeSurfaceMetadata,
              Cordis.SessionRefinement.decodeRequiredString,
              Cordis.SessionRefinement.decodeRequiredNat,
              Cordis.SessionRefinement.decodeOptionalWireUsage,
              Cordis.SessionRefinement.requireField,
              Cordis.SessionRefinement.rejectPresent,
              Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
              Cordis.SessionRefinement.decodeString, safeNat_decode,
              safeNatList_decode]
            rfl
      | some usage =>
          let sourceMessage : WireAssistantMessage := {
            id := id
            provider := provider
            model := model
            content := blocks
            usage := none }
          have decodedMessage :
              decodeAssistantMessage [.field "data", .field "message"]
                (assistantMessageJson sourceMessage content) = .ok sourceMessage :=
            assistantMessage_decode [.field "data", .field "message"] sourceMessage
              encodedContent
          have decodedUsage :
              decodeWireUsage [.field "data", .field "usage"] (wireUsageJson usage) = .ok usage :=
            wireUsage_decode [.field "data", .field "usage"] usage
          have decodedMessage' := decodedMessage
          simp only [assistantMessageJson, assistantSourceJson, rawObj] at decodedMessage'
          dsimp [sourceMessage] at decodedMessage'
          have decodedUsage' := decodedUsage
          simp only [wireUsageJson, rawObj] at decodedUsage'
          cases sourceEventSeqs <;> cases surfaceOp <;>
            simp only [assistantEventJsonWithMetadata, eventObj, assistantMessageJson,
              assistantSourceJson, rawObj, wireUsageFields, surfaceFields, surfaceOpJson,
              sourceEventSeqsFields, decodeEvent]
          all_goals
            unfold Cordis.SessionRefinement.decodeEventAt
            simp_all (maxSteps := 1000000) [Bind.bind, Except.bind,
              Cordis.SessionRefinement.decodePayload,
              Cordis.SessionRefinement.decodeAssistantMessageData,
              Cordis.SessionRefinement.decodeSurfaceMetadata,
              Cordis.SessionRefinement.decodeRequiredString,
              Cordis.SessionRefinement.decodeRequiredNat,
              Cordis.SessionRefinement.decodeOptionalWireUsage,
              Cordis.SessionRefinement.requireField,
              Cordis.SessionRefinement.rejectPresent,
              Cordis.SessionRefinement.field?, Cordis.SessionRefinement.fieldPath,
              Cordis.SessionRefinement.decodeString, safeNat_decode,
              safeNatList_decode, wireUsageJson, rawObj]
            rfl

theorem decode_encode {event : WireEvent} {json : Lean.Json}
    (encoded : encodeWireEvent event = .ok json) :
    decodeEvent json = .ok event := by
  cases event with
  | mk seq time payload =>
      cases payload with
      | userMessage append =>
          cases append with
          | mk message sourceEventSeqs surfaceOp =>
              cases message with
              | user message =>
                  cases encoded
                  exact decode_userMessage seq time message sourceEventSeqs surfaceOp
              | assistant message =>
                  simp [encodeWireEvent, encodeUserMessage] at encoded
      | toolResult result =>
          cases encoded
          exact decode_toolResult seq time result
      | assistantMessage turn step append =>
          cases append with
          | mk message sourceEventSeqs surfaceOp =>
              cases message with
              | user message =>
                  simp_all [encodeWireEvent, encodeAssistantMessage, Bind.bind, Except.bind]
              | assistant message =>
                  cases hContent : assistantBlocksJson message.content with
                  | error error =>
                      simp_all [encodeWireEvent, encodeAssistantMessage, Bind.bind, Except.bind]
                  | ok content =>
                      simp only [encodeWireEvent, encodeAssistantMessage, Bind.bind, Except.bind]
                        at encoded
                      rw [hContent] at encoded
                      cases encoded
                      exact decode_assistantMessage_withMetadata seq time turn step message
                        sourceEventSeqs surfaceOp hContent
      | turnStart turn =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .turnStart turn } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | turnEnd reason nextStep =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .turnEnd reason nextStep } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | stepStart turn step =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .stepStart turn step } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | stepEnd turn step =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .stepEnd turn step } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | requestContext context =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .requestContext context } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | sessionEndSeed =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .sessionEndSeed } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | assistantChunk chunk =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .assistantChunk chunk } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | assistantReasoningChunk chunk =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .assistantReasoningChunk chunk } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | toolCall turn step callId name arguments =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .toolCall turn step callId name arguments } =
                .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | todoWrite todos =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .todoWrite todos } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar
      | requestHeader header =>
          have scalar :
              Cordis.SessionRefinement.Codec.encodeWireEvent
                { seq, time, payload := .requestHeader header } = .ok json := by
            apply scalar_mapError_ok
            simpa [encodeWireEvent] using encoded
          exact Cordis.SessionRefinement.Codec.decode_encode scalar

inductive TextDecodeError where
  | text (error : TextRefinement.TextError)
  | empty
  | multiple (count : Nat)
  | semantic (error : DecodeError)
  deriving BEq, DecidableEq, Repr

private def decodeSemantic (json : Lean.Json) : Except TextDecodeError WireEvent :=
  (decodeEvent json).mapError TextDecodeError.semantic

private def decodeSemanticLines (jsons : List Lean.Json) :
    Except TextDecodeError (List WireEvent) :=
  (jsons.mapM decodeEvent).mapError TextDecodeError.semantic

/-- Encode one admitted event as compact newline-delimited JSON text. -/
def encodeWireEventLine (event : WireEvent) : Except EncodeError String :=
  (encodeWireEvent event).map Lean.Json.compress

/-- Parse exactly one JSON line and run the source-shaped semantic decoder. -/
def decodeWireEventLine (text : String) : Except TextDecodeError WireEvent :=
  match _parsed : TextRefinement.parseJsonLines text with
  | .error error => .error (.text error)
  | .ok [] => .error .empty
  | .ok [json] => decodeSemantic json
  | .ok (_first :: _second :: rest) => .error (.multiple (rest.length + 2))

/-- Encode a finite admitted event list as canonical JSONL text. -/
def encodeWireEventsText (events : List WireEvent) : Except EncodeError String :=
  (events.mapM encodeWireEvent).map TextRefinement.renderJsonLines

/-- Decode finite JSONL text through this surface codec. -/
def decodeWireEventsText (text : String) :
    Except TextDecodeError (List WireEvent) :=
  match _parsed : TextRefinement.parseJsonLines text with
  | .error error => .error (.text error)
  | .ok jsons => decodeSemanticLines jsons

/-- Encode a finite admitted event list as canonical UTF-8 JSONL bytes. -/
def encodeWireEventsBytes (events : List WireEvent) : Except EncodeError ByteArray :=
  (events.mapM encodeWireEvent).map TextRefinement.renderJsonLinesBytes

/-- Decode canonical UTF-8 JSONL bytes through this surface codec. -/
def decodeWireEventsBytes (source : ByteArray) :
    Except TextDecodeError (List WireEvent) :=
  match _parsed : TextRefinement.parseJsonLinesBytes source with
  | .error error => .error (.text error)
  | .ok jsons => decodeSemanticLines jsons

theorem encodeWireEventLine_eq_compress
    {event : WireEvent} {json : Lean.Json}
    (encoded : encodeWireEvent event = .ok json) :
    encodeWireEventLine event = .ok (Lean.Json.compress json) := by
  change (encodeWireEvent event).map Lean.Json.compress = .ok (Lean.Json.compress json)
  rw [encoded]
  rfl

theorem decodeWireEventLine_of_encoded
    {event : WireEvent} {json : Lean.Json} {text : String}
    (encoded : encodeWireEvent event = .ok json)
    (parsed : TextRefinement.parseJsonLines text = .ok [json]) :
    decodeWireEventLine text = .ok event := by
  unfold decodeWireEventLine
  generalize h : TextRefinement.parseJsonLines text = result
  cases result with
  | error error => simp_all
  | ok lines =>
      cases lines with
      | nil => simp_all
      | cons first rest =>
          cases rest with
          | nil =>
              have lines_eq :
                  (Except.ok [first] : Except TextRefinement.TextError (List Lean.Json)) =
                    .ok [json] := h.symm.trans parsed
              cases lines_eq
              simp [decodeSemantic, decode_encode encoded, Except.mapError]
          | cons second rest => simp_all

private theorem map_decode_of_encoded :
    ∀ {events : List WireEvent} {jsons : List Lean.Json},
      events.mapM encodeWireEvent = .ok jsons →
      jsons.mapM decodeEvent = .ok events := by
  intro events
  induction events with
  | nil =>
      intro jsons h
      rw [List.mapM_nil] at h
      cases h
      rfl
  | cons event events ih =>
      intro jsons h
      rw [List.mapM_cons] at h
      cases hHead : encodeWireEvent event with
      | error error =>
          simp [hHead] at h
          contradiction
      | ok encodedEvent =>
          rw [hHead] at h
          cases hTail : List.mapM encodeWireEvent events with
          | error error =>
              simp [hTail] at h
              contradiction
          | ok encodedTail =>
              rw [hTail] at h
              cases h
              rw [List.mapM_cons]
              rw [show decodeEvent encodedEvent = .ok event from decode_encode hHead]
              rw [ih hTail]
              rfl

theorem decodeWireEventsText_of_encoded
    {events : List WireEvent} {jsons : List Lean.Json} {text : String}
    (encoded : events.mapM encodeWireEvent = .ok jsons)
    (parsed : TextRefinement.parseJsonLines text = .ok jsons) :
    decodeWireEventsText text = .ok events := by
  have decoded : jsons.mapM decodeEvent = .ok events := map_decode_of_encoded encoded
  unfold decodeWireEventsText
  generalize h : TextRefinement.parseJsonLines text = result
  cases result with
  | error error => simp_all
  | ok lines =>
      have lines_eq :
          (Except.ok lines : Except TextRefinement.TextError (List Lean.Json)) =
            .ok jsons := h.symm.trans parsed
      cases lines_eq
      simp [decodeSemanticLines, decoded, Except.mapError]

theorem decodeWireEventsBytes_of_encoded
    {events : List WireEvent} {jsons : List Lean.Json} {source : ByteArray}
    (encoded : events.mapM encodeWireEvent = .ok jsons)
    (parsed : TextRefinement.parseJsonLinesBytes source = .ok jsons) :
    decodeWireEventsBytes source = .ok events := by
  have decoded : jsons.mapM decodeEvent = .ok events := map_decode_of_encoded encoded
  unfold decodeWireEventsBytes
  generalize h : TextRefinement.parseJsonLinesBytes source = result
  cases result with
  | error error => simp_all
  | ok lines =>
      have lines_eq :
          (Except.ok lines : Except TextRefinement.TextError (List Lean.Json)) =
            .ok jsons := h.symm.trans parsed
      cases lines_eq
      simp [decodeSemanticLines, decoded, Except.mapError]

def executableUserMessage : WireUserMessage := {
  id := "user-surface"
  content := [{ text := "weather?" }]
}

def executableToolResult : WireToolResult := {
  turn := { value := 1, safe := by decide }
  step := { value := 1, safe := by decide }
  messageId := "tool-message"
  sourceCallId := "call-weather"
  blockCallId := "call-weather"
  content := "weather unavailable"
  isError := true
  sourceEventSeqs := [{ value := 4, safe := by decide }]
  surfaceOp := .replace { value := 3, safe := by decide } { value := 5, safe := by decide }
}

def executableSurfaceEvents : List WireEvent := [
  { seq := { value := 6, safe := by decide }
    time := { value := 106, safe := by decide }
    payload := .userMessage {
      message := .user executableUserMessage
      sourceEventSeqs := some [{ value := 2, safe := by decide }]
      surfaceOp := .append
    } },
  { seq := { value := 7, safe := by decide }
    time := { value := 107, safe := by decide }
    payload := .toolResult executableToolResult }
]

theorem executableSurfaceEvents_encodable :
    ∃ jsons, executableSurfaceEvents.mapM encodeWireEvent = .ok jsons := by
  refine ⟨[userEventJson { value := 6, safe := by decide } { value := 106, safe := by decide } {
    message := .user executableUserMessage
    sourceEventSeqs := some [{ value := 2, safe := by decide }]
    surfaceOp := .append
  }, toolResultEvent { value := 7, safe := by decide } { value := 107, safe := by decide }
      executableToolResult], ?_⟩
  simp only [executableSurfaceEvents, List.mapM_cons, List.mapM_nil, encodeWireEvent,
    encodeUserMessage, encodeToolResult]
  rfl

def executableAssistantMessage : WireAssistantMessage := {
  id := "assistant-surface"
  provider := "fixture-provider"
  model := "fixture-model"
  content := [.text "forecast", .reasoning "checked",
    .image (rawObj [("type", .str "image"), ("mimeType", .str "image/png"),
      ("url", .str "https://example.invalid/forecast.png"),
      ("alt", .str "forecast")]),
    .toolCall "call-weather" "weather" "{\"city\":\"Cupertino\"}"]
  usage := some {
    inputTokens := { value := 11, safe := by decide }
    outputTokens := { value := 7, safe := by decide }
    cacheReadTokens := some { value := 3, safe := by decide }
    cacheWriteTokens := none
    reasoningTokens := some { value := 2, safe := by decide }
  }
}

def executableAssistantEvent : WireEvent := {
  seq := { value := 8, safe := by decide }
  time := { value := 108, safe := by decide }
  payload := .assistantMessage { value := 1, safe := by decide } { value := 2, safe := by decide } {
    message := .assistant executableAssistantMessage
    sourceEventSeqs := some [{ value := 6, safe := by decide }]
    surfaceOp := .replace { value := 3, safe := by decide } { value := 5, safe := by decide }
  }
}

theorem executableAssistantEvent_encodable :
    ∃ json, encodeWireEvent executableAssistantEvent = .ok json := by
  let content : Lean.Json := .arr #[
    rawObj [("type", .str "text"), ("text", .str "forecast")],
    rawObj [("type", .str "reasoning"), ("text", .str "checked")],
    rawObj [("type", .str "image"), ("mimeType", .str "image/png"),
      ("url", .str "https://example.invalid/forecast.png"),
      ("alt", .str "forecast")],
    rawObj [("type", .str "tool-call"), ("id", .str "call-weather"),
      ("name", .str "weather"), ("arguments", .str "{\"city\":\"Cupertino\"}")]]
  refine ⟨assistantEventJsonWithMetadata { value := 8, safe := by decide }
    { value := 108, safe := by decide } { value := 1, safe := by decide }
    { value := 2, safe := by decide } executableAssistantMessage content
    (some [{ value := 6, safe := by decide }])
    (.replace { value := 3, safe := by decide } { value := 5, safe := by decide }), ?_⟩
  simp only [executableAssistantEvent, encodeWireEvent, encodeAssistantMessage,
    executableAssistantMessage, assistantBlocksJson, assistantBlockJson, List.mapM_cons,
    List.mapM_nil, Bind.bind, Except.bind, content, assistantEventJsonWithMetadata]
  rfl

end Cordis.SessionRefinement.SurfaceCodec
