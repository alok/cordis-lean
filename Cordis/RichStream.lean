import Std

/-!
# Proof-carrying rich LLM streams

This module is a finite Lean model of the core contract documented by DeepSeek Harness commit
`99f6f02` in `docs/subsystems/llm-streaming.md`. Provider chunks remain untrusted until validation
constructs an indexed `Event` or `Trace` witness.

The model retains interleaved text, reasoning, and tool-call blocks in first-seen index order.
Tool arguments stay raw JSON strings and are concatenated without parsing or normalization.
Images, tool-result blocks, provider transport, and truncation/pruning are deliberately outside
this slice. Replay metadata is accepted only when already aligned with the retained final blocks;
an integration that prunes blocks must prune metadata before calling this validator.

`AssistantMessageView` is the integration boundary with `Cordis.Session`: its `content` and
`rawToolCalls` fields correspond to an assistant payload. The session layer must assign its own
numeric `CallId` values to provider string identifiers and supply the enclosing turn and step.
-/

set_option autoImplicit false

namespace Cordis.RichStream

/-- The three block kinds implemented by this finite streaming core. -/
inductive BlockKind where
  | text
  | reasoning
  | toolCall
  deriving BEq, DecidableEq, Repr

/-- A completely assembled retained assistant block. Tool arguments are deliberately raw JSON. -/
inductive ContentBlock where
  | text (content : String)
  | reasoning (content : String)
  | toolCall (id name rawArguments : String)
  deriving BEq, DecidableEq, Repr

/-- A tool call can be incomplete while its provider deltas are still arriving. -/
structure ToolAccumulator where
  id : Option String := none
  name : Option String := none
  rawArguments : String := ""
  deriving BEq, DecidableEq, Repr

/-- The accumulator type selected by a block kind. -/
def Accumulator : BlockKind → Type
  | .text => String
  | .reasoning => String
  | .toolCall => ToolAccumulator

/-- Initial accumulator allocated by a contiguous block-start event. -/
def initialAccumulator : (kind : BlockKind) → Accumulator kind
  | .text => ""
  | .reasoning => ""
  | .toolCall => {}

/-- A tool delta repeats its stable id, may introduce/repeat its name, and appends raw arguments. -/
structure ToolDelta where
  id : String
  name : Option String
  argumentsDelta : String
  deriving BEq, DecidableEq, Repr

/-- Kind-indexed deltas make cross-kind updates ill-typed in trusted code. -/
inductive Delta : (kind : BlockKind) → Type where
  | text (fragment : String) : Delta .text
  | reasoning (fragment : String) : Delta .reasoning
  | toolCall (fragment : ToolDelta) : Delta .toolCall

/-- A slot is either open with its kind-selected accumulator or closed with its exact block. -/
inductive BlockSlot where
  | open (kind : BlockKind) (accumulator : Accumulator kind)
  | closed (block : ContentBlock)

/-- Token accounting is emitted once, before the terminal finish chunk. -/
structure TokenUsage where
  inputTokens : Nat
  outputTokens : Nat
  cacheReadTokens : Nat := 0
  cacheWriteTokens : Nat := 0
  reasoningTokens : Nat := 0
  deriving BEq, DecidableEq, Repr

/-- A structured provider failure retained in the terminal reason. -/
structure StructuredFailure where
  code : String
  message : String
  retryable : Bool
  deriving BEq, DecidableEq, Repr

/-- Machine-readable categories for a caller or runtime abort. -/
inductive AbortKind where
  | callerCancelled
  | timeout
  | shutdown
  deriving BEq, DecidableEq, Repr

/-- A structured abort cause retained in the terminal reason. -/
structure AbortCause where
  kind : AbortKind
  detail : String
  deriving BEq, DecidableEq, Repr

/-- Every successful, failed, or aborted finish is a terminal stream reason. -/
inductive FinishReason where
  | stop
  | toolCalls
  | maxTokens
  | error (failure : StructuredFailure)
  | aborted (cause : AbortCause)
  deriving BEq, DecidableEq, Repr

/-- Provider metadata associated with one retained block, when the provider supplied any. -/
structure BlockMetadata where
  providerBlockId : Option String := none
  signature : Option String := none
  deriving BEq, DecidableEq, Repr

/-- Per-block metadata whose length is tied to the retained block count by a proof. -/
structure AlignedMetadata (blocks : List ContentBlock) where
  entries : List (Option BlockMetadata)
  length_eq : entries.length = blocks.length

/-- Successful replay metadata indexed by the exact final retained block list. -/
structure ReplayEnvelope (blocks : List ContentBlock) where
  responseId : Option String
  perBlock : AlignedMetadata blocks

/-- The proof field exposes alignment directly to downstream trusted code. -/
theorem AlignedMetadata.hasFinalBlockCount {blocks : List ContentBlock}
    (metadata : AlignedMetadata blocks) : metadata.entries.length = blocks.length :=
  metadata.length_eq

/-- Proof-free replay data arriving at the runtime boundary. -/
structure RawReplayEnvelope where
  responseId : Option String
  perBlock : List (Option BlockMetadata)
  deriving BEq, DecidableEq, Repr

namespace ReplayEnvelope

/-- Erase only the alignment proof, retaining the exact replay data. -/
def erase {blocks : List ContentBlock} (replay : ReplayEnvelope blocks) : RawReplayEnvelope := {
  responseId := replay.responseId
  perBlock := replay.perBlock.entries
}

end ReplayEnvelope

/-- Static stream states retain exact open slots, usage, blocks, reason, and aligned replay data. -/
inductive State where
  | active (slots : List BlockSlot) (usage : Option TokenUsage)
  | terminal (blocks : List ContentBlock) (usage : TokenUsage) (reason : FinishReason)
      (replay : Option (ReplayEnvelope blocks))

namespace State

/-- The empty stream has no allocated block slots and no usage chunk. -/
def initial : State :=
  .active [] none

end State

/-- Untrusted provider chunks in the DeepSeek Harness streaming vocabulary. -/
inductive RawChunk where
  | blockStart (index : Nat) (kind : BlockKind)
  | textDelta (index : Nat) (fragment : String)
  | reasoningDelta (index : Nat) (fragment : String)
  | toolCallDelta (index : Nat) (fragment : ToolDelta)
  | blockEnd (index : Nat) (assembled : ContentBlock)
  | usage (tokens : TokenUsage)
  | finish (reason : FinishReason) (replay : Option RawReplayEnvelope)
  deriving BEq, DecidableEq, Repr

/-- Exact, fail-closed reasons why a raw provider chunk cannot extend the stream. -/
inductive ValidationError where
  | wrongStartIndex (expected actual : Nat)
  | missingIndex (index : Nat)
  | closedIndex (index : Nat)
  | deltaKindMismatch (index : Nat) (expected actual : BlockKind)
  | toolCallIdMismatch (index : Nat) (expected actual : String)
  | toolCallNameMismatch (index : Nat) (expected actual : String)
  | incompleteToolCall (index : Nat) (missingId missingName : Bool)
  | blockEndMismatch (index : Nat) (expected actual : ContentBlock)
  | duplicateUsage
  | finishWithoutUsage
  | finishWithOpenBlocks (indices : List Nat)
  | metadataLengthMismatch (expected actual : Nat)
  | postFinish (chunk : RawChunk)
  deriving BEq, DecidableEq, Repr

/-- Update a stable optional tool-call field, rejecting a conflicting repeated value. -/
private def mergeStableField (index : Nat) (isId : Bool) (current : Option String)
    (incoming : String) : Except ValidationError (Option String) :=
  match current with
  | none => .ok (some incoming)
  | some expected =>
      if expected = incoming then
        .ok current
      else if isId then
        .error (.toolCallIdMismatch index expected incoming)
      else
        .error (.toolCallNameMismatch index expected incoming)

/-- Apply one well-kinded delta to its kind-selected accumulator. -/
def applyDelta (index : Nat) : (kind : BlockKind) → (accumulator : Accumulator kind) →
    Delta kind → Except ValidationError (Accumulator kind)
  | .text, accumulator, .text fragment => .ok (String.append accumulator fragment)
  | .reasoning, accumulator, .reasoning fragment => .ok (String.append accumulator fragment)
  | .toolCall, accumulator, .toolCall fragment => do
      let id ← mergeStableField index true accumulator.id fragment.id
      let name ← match fragment.name with
        | none => .ok accumulator.name
        | some incoming => mergeStableField index false accumulator.name incoming
      .ok { id, name, rawArguments := accumulator.rawArguments ++ fragment.argumentsDelta }

/-- Convert a complete accumulator to its exact content block, if all required fields exist. -/
def completeAccumulator : {kind : BlockKind} → Accumulator kind → Option ContentBlock
  | .text, content => some (.text content)
  | .reasoning, content => some (.reasoning content)
  | .toolCall, accumulator => do
      let id ← accumulator.id
      let name ← accumulator.name
      some (.toolCall id name accumulator.rawArguments)

/-- Lift an error reported relative to a tail so it names the original absolute block index. -/
private def shiftError : ValidationError → ValidationError
  | .missingIndex index => .missingIndex (index + 1)
  | .closedIndex index => .closedIndex (index + 1)
  | .deltaKindMismatch index expected actual =>
      .deltaKindMismatch (index + 1) expected actual
  | .toolCallIdMismatch index expected actual =>
      .toolCallIdMismatch (index + 1) expected actual
  | .toolCallNameMismatch index expected actual =>
      .toolCallNameMismatch (index + 1) expected actual
  | .incompleteToolCall index missingId missingName =>
      .incompleteToolCall (index + 1) missingId missingName
  | .blockEndMismatch index expected actual =>
      .blockEndMismatch (index + 1) expected actual
  | error => error

/-- Update one absolute slot index; recursive tail errors are shifted back to the root. -/
def updateSlotAt (slots : List BlockSlot) (index : Nat) (kind : BlockKind)
    (delta : Delta kind) : Except ValidationError (List BlockSlot) :=
  match slots, index with
  | [], index => .error (.missingIndex index)
  | .closed _ :: _, 0 => .error (.closedIndex 0)
  | .open actual accumulator :: rest, 0 =>
      if same : actual = kind then
        match same with
        | rfl => do
            let updated ← applyDelta 0 actual accumulator delta
            .ok (.open actual updated :: rest)
      else
        .error (.deltaKindMismatch 0 actual kind)
  | slot :: rest, index + 1 =>
      match updateSlotAt rest index kind delta with
      | .ok updated => .ok (slot :: updated)
      | .error error => .error (shiftError error)

/-- Close exactly one slot, checking that the provider's block is the exact assembled value. -/
def closeSlotAt (slots : List BlockSlot) (index : Nat)
    (assembled : ContentBlock) : Except ValidationError (List BlockSlot) :=
  match slots, index with
  | [], index => .error (.missingIndex index)
  | .closed _ :: _, 0 => .error (.closedIndex 0)
  | .open .toolCall accumulator :: rest, 0 =>
      match accumulator.id, accumulator.name with
      | none, none => .error (.incompleteToolCall 0 true true)
      | none, some _ => .error (.incompleteToolCall 0 true false)
      | some _, none => .error (.incompleteToolCall 0 false true)
      | some id, some name =>
          let expected := .toolCall id name accumulator.rawArguments
          if expected = assembled then
            .ok (.closed assembled :: rest)
          else
            .error (.blockEndMismatch 0 expected assembled)
  | .open .text accumulator :: rest, 0 =>
      let expected := .text accumulator
      if expected = assembled then
        .ok (.closed assembled :: rest)
      else
        .error (.blockEndMismatch 0 expected assembled)
  | .open .reasoning accumulator :: rest, 0 =>
      let expected := .reasoning accumulator
      if expected = assembled then
        .ok (.closed assembled :: rest)
      else
        .error (.blockEndMismatch 0 expected assembled)
  | slot :: rest, index + 1 =>
      match closeSlotAt rest index assembled with
      | .ok updated => .ok (slot :: updated)
      | .error error => .error (shiftError error)

/-- Collect closed blocks in first-seen slot order; return `none` if any slot remains open. -/
def closedBlocks? : List BlockSlot → Option (List ContentBlock)
  | [] => some []
  | .open _ _ :: _ => none
  | .closed block :: rest => do
      let blocks ← closedBlocks? rest
      some (block :: blocks)

/-- Absolute indices of every still-open slot. -/
def openIndices (slots : List BlockSlot) : List Nat :=
  let rec loop : Nat → List BlockSlot → List Nat
    | _, [] => []
    | index, .open _ _ :: rest => index :: loop (index + 1) rest
    | index, .closed _ :: rest => loop (index + 1) rest
  loop 0 slots

/--
The trusted transition API. Every constructor fixes both predecessor and successor. There is no
constructor whose predecessor is terminal.
-/
inductive Event : State → State → Type where
  | blockStart {slots : List BlockSlot} {usage : Option TokenUsage} (kind : BlockKind) :
      Event (.active slots usage)
        (.active (slots ++ [.open kind (initialAccumulator kind)]) usage)
  | delta {slots nextSlots : List BlockSlot} {usage : Option TokenUsage}
      {kind : BlockKind} (index : Nat) (change : Delta kind)
      (applied : updateSlotAt slots index kind change = .ok nextSlots) :
      Event (.active slots usage) (.active nextSlots usage)
  | blockEnd {slots nextSlots : List BlockSlot} {usage : Option TokenUsage}
      (index : Nat) (assembled : ContentBlock)
      (closed : closeSlotAt slots index assembled = .ok nextSlots) :
      Event (.active slots usage) (.active nextSlots usage)
  | usage {slots : List BlockSlot} (tokens : TokenUsage) :
      Event (.active slots none) (.active slots (some tokens))
  | finish {slots : List BlockSlot} {blocks : List ContentBlock} {tokens : TokenUsage}
      (reason : FinishReason) (replay : Option (ReplayEnvelope blocks))
      (closed : closedBlocks? slots = some blocks) :
      Event (.active slots (some tokens)) (.terminal blocks tokens reason replay)

/-- No typed event can follow any terminal finish reason, including error and abort. -/
theorem noEventAfterTerminal {blocks : List ContentBlock} {usage : TokenUsage}
    {reason : FinishReason} {replay : Option (ReplayEnvelope blocks)} {next : State}
    (event : Event (.terminal blocks usage reason replay) next) : False := by
  cases event

/-- In particular, a terminal transition cannot occur before the unique usage event. -/
theorem noFinishWithoutUsage {slots : List BlockSlot} {blocks : List ContentBlock}
    {usage : TokenUsage}
    {reason : FinishReason} {replay : Option (ReplayEnvelope blocks)}
    (event : Event (.active slots none) (.terminal blocks usage reason replay)) : False := by
  cases event

/-- A compositional proof-carrying stream trace. -/
inductive Trace : State → State → Type where
  | nil {state : State} : Trace state state
  | cons {start middle finish : State} :
      Event start middle → Trace middle finish → Trace start finish

namespace Trace

/-- Compose traces at their definitionally shared boundary state. -/
def append {start middle finish : State} :
    Trace start middle → Trace middle finish → Trace start finish
  | .nil, suffix => suffix
  | .cons event rest, suffix => .cons event (append rest suffix)

/-- Regard one event as a one-element trace. -/
def single {start finish : State} (event : Event start finish) : Trace start finish :=
  .cons event .nil

end Trace

/-- Runtime state retains all data except replay alignment proofs. -/
inductive RuntimeState where
  | active (slots : List BlockSlot) (usage : Option TokenUsage)
  | terminal (blocks : List ContentBlock) (usage : TokenUsage) (reason : FinishReason)
      (replay : Option RawReplayEnvelope)

namespace RuntimeState

/-- Runtime counterpart of `State.initial`. -/
def initial : RuntimeState :=
  .active [] none

end RuntimeState

/-- Forget static indices and alignment proofs while preserving exact runtime data. -/
def eraseState : State → RuntimeState
  | .active slots usage => .active slots usage
  | .terminal blocks usage reason replay =>
      .terminal blocks usage reason (replay.map ReplayEnvelope.erase)

@[simp] theorem eraseState_active (slots : List BlockSlot) (usage : Option TokenUsage) :
    eraseState (.active slots usage) = .active slots usage :=
  rfl

@[simp] theorem eraseState_terminal (blocks : List ContentBlock) (usage : TokenUsage)
    (reason : FinishReason) (replay : Option (ReplayEnvelope blocks)) :
    eraseState (.terminal blocks usage reason replay) =
      .terminal blocks usage reason (replay.map ReplayEnvelope.erase) :=
  rfl

namespace Event

/-- Forget transition proofs while preserving the exact provider chunk. -/
def erase {start finish : State} : Event start finish → RawChunk
  | .blockStart (slots := slots) kind => .blockStart slots.length kind
  | .delta index (.text fragment) _ => .textDelta index fragment
  | .delta index (.reasoning fragment) _ => .reasoningDelta index fragment
  | .delta index (.toolCall fragment) _ => .toolCallDelta index fragment
  | .blockEnd index assembled _ => .blockEnd index assembled
  | .usage tokens => .usage tokens
  | .finish reason replay _ => .finish reason (replay.map ReplayEnvelope.erase)

end Event

namespace Trace

/-- Erase a typed trace to the exact raw provider chunk list. -/
def erase {start finish : State} : Trace start finish → List RawChunk
  | .nil => []
  | .cons event rest => event.erase :: rest.erase

end Trace

/-- Validate replay metadata length without trusting provider convention. -/
private def validateReplayLength (blocks : List ContentBlock)
    (replay : Option RawReplayEnvelope) : Except ValidationError Unit :=
  match replay with
  | none => .ok ()
  | some replay =>
      if replay.perBlock.length = blocks.length then
        .ok ()
      else
        .error (.metadataLengthMismatch blocks.length replay.perBlock.length)

/-- Apply one raw chunk to the proof-free runtime state. -/
def applyRaw (state : RuntimeState) (chunk : RawChunk) :
    Except ValidationError RuntimeState :=
  match state with
  | .terminal _ _ _ _ => .error (.postFinish chunk)
  | .active slots usage =>
      match chunk with
      | .blockStart index kind =>
          if index = slots.length then
            .ok (.active (slots ++ [.open kind (initialAccumulator kind)]) usage)
          else
            .error (.wrongStartIndex slots.length index)
      | .textDelta index fragment => do
          let updated ← updateSlotAt slots index .text (.text fragment)
          .ok (.active updated usage)
      | .reasoningDelta index fragment => do
          let updated ← updateSlotAt slots index .reasoning (.reasoning fragment)
          .ok (.active updated usage)
      | .toolCallDelta index fragment => do
          let updated ← updateSlotAt slots index .toolCall (.toolCall fragment)
          .ok (.active updated usage)
      | .blockEnd index assembled => do
          let updated ← closeSlotAt slots index assembled
          .ok (.active updated usage)
      | .usage tokens =>
          match usage with
          | none => .ok (.active slots (some tokens))
          | some _ => .error .duplicateUsage
      | .finish reason replay =>
          match usage with
          | none => .error .finishWithoutUsage
          | some tokens =>
              match closedBlocks? slots with
              | none => .error (.finishWithOpenBlocks (openIndices slots))
              | some blocks => do
                  validateReplayLength blocks replay
                  .ok (.terminal blocks tokens reason replay)

/-- Validate and replay raw chunks from left to right. -/
def replayRaw : RuntimeState → List RawChunk → Except ValidationError RuntimeState
  | state, [] => .ok state
  | state, chunk :: rest => do
      let next ← applyRaw state chunk
      replayRaw next rest

/-- One raw replay envelope reconstructed with a block-count alignment proof. -/
structure ValidatedReplayEnvelope (blocks : List ContentBlock) (raw : RawReplayEnvelope) where
  value : ReplayEnvelope blocks
  erase_eq : value.erase = raw

/-- Produce the dependent replay envelope only after checking its exact retained-block count. -/
def validateReplayEnvelope (blocks : List ContentBlock) (raw : RawReplayEnvelope) :
    Except ValidationError (ValidatedReplayEnvelope blocks raw) :=
  if aligned : raw.perBlock.length = blocks.length then
    .ok {
      value := {
        responseId := raw.responseId
        perBlock := { entries := raw.perBlock, length_eq := aligned }
      }
      erase_eq := rfl
    }
  else
    .error (.metadataLengthMismatch blocks.length raw.perBlock.length)

/-- A raw chunk reconstructed as an intrinsic transition with exact erasure. -/
structure ValidatedChunk (start : State) (raw : RawChunk) where
  finish : State
  event : Event start finish
  erase_eq : event.erase = raw

/-- Proof-producing one-chunk validator. -/
def validateChunk : (start : State) → (raw : RawChunk) →
    Except ValidationError (ValidatedChunk start raw)
  | .terminal blocks usage reason replay, raw => .error (.postFinish raw)
  | .active slots usage, .blockStart index kind =>
      if contiguous : index = slots.length then
        .ok {
          finish := .active (slots ++ [.open kind (initialAccumulator kind)]) usage
          event := .blockStart kind
          erase_eq := by
            change RawChunk.blockStart slots.length kind = RawChunk.blockStart index kind
            rw [contiguous]
        }
      else
        .error (.wrongStartIndex slots.length index)
  | .active slots usage, .textDelta index fragment =>
      match applied : updateSlotAt slots index .text (.text fragment) with
      | .error error => .error error
      | .ok nextSlots => .ok {
          finish := .active nextSlots usage
          event := .delta index (.text fragment) applied
          erase_eq := rfl
        }
  | .active slots usage, .reasoningDelta index fragment =>
      match applied : updateSlotAt slots index .reasoning (.reasoning fragment) with
      | .error error => .error error
      | .ok nextSlots => .ok {
          finish := .active nextSlots usage
          event := .delta index (.reasoning fragment) applied
          erase_eq := rfl
        }
  | .active slots usage, .toolCallDelta index fragment =>
      match applied : updateSlotAt slots index .toolCall (.toolCall fragment) with
      | .error error => .error error
      | .ok nextSlots => .ok {
          finish := .active nextSlots usage
          event := .delta index (.toolCall fragment) applied
          erase_eq := rfl
        }
  | .active slots usage, .blockEnd index assembled =>
      match closed : closeSlotAt slots index assembled with
      | .error error => .error error
      | .ok nextSlots => .ok {
          finish := .active nextSlots usage
          event := .blockEnd index assembled closed
          erase_eq := rfl
        }
  | .active slots none, .usage tokens => .ok {
      finish := .active slots (some tokens)
      event := .usage tokens
      erase_eq := rfl
    }
  | .active _ (some _), .usage _ => .error .duplicateUsage
  | .active _ none, .finish _ _ => .error .finishWithoutUsage
  | .active slots (some tokens), .finish reason rawReplay =>
      match allClosed : closedBlocks? slots with
      | none => .error (.finishWithOpenBlocks (openIndices slots))
      | some blocks =>
          match rawReplay with
          | none => .ok {
              finish := .terminal blocks tokens reason none
              event := .finish reason none allClosed
              erase_eq := rfl
            }
          | some raw =>
              match validateReplayEnvelope blocks raw with
              | .error error => .error error
              | .ok validated => .ok {
                  finish := .terminal blocks tokens reason (some validated.value)
                  event := .finish reason (some validated.value) allClosed
                  erase_eq := by simp [Event.erase, validated.erase_eq]
                }

/-- A whole raw list reconstructed as a compositional intrinsic trace with exact erasure. -/
structure ValidatedTrace (start : State) (raw : List RawChunk) where
  finish : State
  trace : Trace start finish
  erase_eq : trace.erase = raw

/-- Proof-producing validator for a finite raw trace, whether complete or still active. -/
def validateTrace : (start : State) → (raw : List RawChunk) →
    Except ValidationError (ValidatedTrace start raw)
  | start, [] => .ok { finish := start, trace := .nil, erase_eq := rfl }
  | start, chunk :: rest => do
      let first ← validateChunk start chunk
      let suffix ← validateTrace first.finish rest
      .ok {
        finish := suffix.finish
        trace := .cons first.event suffix.trace
        erase_eq := by simp [Trace.erase, first.erase_eq, suffix.erase_eq]
      }

/-- Applying an erased typed event reaches exactly its statically indexed successor. -/
@[simp] theorem applyRaw_eraseEvent {start finish : State} (event : Event start finish) :
    applyRaw (eraseState start) event.erase = .ok (eraseState finish) := by
  cases event with
  | blockStart kind => simp [Event.erase, applyRaw, eraseState]
  | delta index change applied =>
      cases change <;> simp [Event.erase, applyRaw, eraseState, applied] <;> rfl
  | blockEnd index assembled closed =>
      simp [Event.erase, applyRaw, eraseState, closed]
      rfl
  | usage tokens => simp [Event.erase, applyRaw, eraseState]
  | @finish slots blocks tokens reason replay closed =>
      cases replay with
      | none =>
          simp [Event.erase, applyRaw, eraseState, closed, validateReplayLength]
          rfl
      | some replay =>
          simp [Event.erase, applyRaw, eraseState, closed, validateReplayLength,
            ReplayEnvelope.erase, replay.perBlock.length_eq]
          rfl

/-- Every erased typed trace replays to its exact statically indexed endpoint. -/
@[simp] theorem replayRaw_eraseTrace {start finish : State} (trace : Trace start finish) :
    replayRaw (eraseState start) trace.erase = .ok (eraseState finish) := by
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      rw [Trace.erase, replayRaw, applyRaw_eraseEvent]
      exact inductionHypothesis

namespace ValidatedChunk

/-- Every validation witness certifies runtime application of its exact original raw chunk. -/
theorem applyRaw_eq {start : State} {raw : RawChunk}
    (validated : ValidatedChunk start raw) :
    applyRaw (eraseState start) raw = .ok (eraseState validated.finish) := by
  calc
    applyRaw (eraseState start) raw =
        applyRaw (eraseState start) validated.event.erase :=
      congrArg (applyRaw (eraseState start)) validated.erase_eq.symm
    _ = .ok (eraseState validated.finish) := applyRaw_eraseEvent validated.event

end ValidatedChunk

namespace ValidatedTrace

/-- Every validation witness certifies replay of its exact original raw list. -/
theorem replayRaw_eq {start : State} {raw : List RawChunk}
    (validated : ValidatedTrace start raw) :
    replayRaw (eraseState start) raw = .ok (eraseState validated.finish) := by
  calc
    replayRaw (eraseState start) raw =
        replayRaw (eraseState start) validated.trace.erase :=
      congrArg (replayRaw (eraseState start)) validated.erase_eq.symm
    _ = .ok (eraseState validated.finish) := replayRaw_eraseTrace validated.trace

end ValidatedTrace

/-- Runtime validation rejects every possible chunk after every terminal reason. -/
theorem applyRaw_afterTerminal (blocks : List ContentBlock) (usage : TokenUsage)
    (reason : FinishReason) (replay : Option RawReplayEnvelope) (chunk : RawChunk) :
    applyRaw (.terminal blocks usage reason replay) chunk = .error (.postFinish chunk) :=
  rfl

/-- A provider-facing tool call in the existing session assistant-message shape. -/
structure ProjectedToolCall where
  providerId : String
  name : String
  rawArguments : String
  deriving BEq, DecidableEq, Repr

/-- Session integration view: visible text plus raw completed tool calls. -/
structure AssistantMessageView where
  content : String
  rawToolCalls : List ProjectedToolCall
  deriving BEq, DecidableEq, Repr

/-- Project retained blocks to the assistant view; reasoning remains private provider data. -/
def toAssistantMessageView (blocks : List ContentBlock) : AssistantMessageView :=
  blocks.foldl (fun view block =>
    match block with
    | .text content => { view with content := view.content ++ content }
    | .reasoning _ => view
    | .toolCall id name rawArguments =>
        { view with rawToolCalls := view.rawToolCalls ++ [{
            providerId := id
            name
            rawArguments
          }] }
  ) { content := "", rawToolCalls := [] }

/-! ## Executable proof-carrying example -/

/-- Expected final blocks, in first-seen rather than block-end order. -/
def interleavedBlocks : List ContentBlock := [
  .text "Hello world",
  .reasoning "plan: check",
  .toolCall "call-a" "lookup" "{\"q\":\"lean\"}",
  .toolCall "call-b" "sum" "{\"xs\":[1,2]}"
]

/-- Usage emitted before the terminal finish. -/
def interleavedUsage : TokenUsage := {
  inputTokens := 10
  outputTokens := 12
  reasoningTokens := 2
}

/-- Four replay entries, one for each retained block. -/
def interleavedReplay : ReplayEnvelope interleavedBlocks := {
  responseId := some "response-1"
  perBlock := {
    entries := [
      some { providerBlockId := some "text-0" },
      none,
      some { providerBlockId := some "tool-2", signature := some "sig-a" },
      some { providerBlockId := some "tool-3", signature := some "sig-b" }
    ]
    length_eq := rfl
  }
}

/-- Text, reasoning, and two tool calls whose deltas are deliberately interleaved by index. -/
def interleavedRaw : List RawChunk := [
  .blockStart 0 .text,
  .textDelta 0 "Hello ",
  .blockStart 1 .reasoning,
  .reasoningDelta 1 "plan:",
  .blockStart 2 .toolCall,
  .toolCallDelta 2 { id := "call-a", name := some "lookup", argumentsDelta := "{\"q\":" },
  .blockStart 3 .toolCall,
  .toolCallDelta 3 { id := "call-b", name := some "sum", argumentsDelta := "{\"xs\":[" },
  .toolCallDelta 2 { id := "call-a", name := none, argumentsDelta := "\"lean\"}" },
  .toolCallDelta 3 { id := "call-b", name := none, argumentsDelta := "1,2]}" },
  .reasoningDelta 1 " check",
  .textDelta 0 "world",
  .blockEnd 3 (.toolCall "call-b" "sum" "{\"xs\":[1,2]}"),
  .blockEnd 0 (.text "Hello world"),
  .blockEnd 2 (.toolCall "call-a" "lookup" "{\"q\":\"lean\"}"),
  .blockEnd 1 (.reasoning "plan: check"),
  .usage interleavedUsage,
  .finish .stop (some interleavedReplay.erase)
]

/-- Intrinsic witness for the entire interleaved example. -/
def interleavedTrace :
    Trace State.initial
      (.terminal interleavedBlocks interleavedUsage .stop (some interleavedReplay)) :=
  .cons (.blockStart .text) <|
  .cons (.delta 0 (.text "Hello ") rfl) <|
  .cons (.blockStart .reasoning) <|
  .cons (.delta 1 (.reasoning "plan:") rfl) <|
  .cons (.blockStart .toolCall) <|
  .cons (.delta 2 (.toolCall {
    id := "call-a", name := some "lookup", argumentsDelta := "{\"q\":"
  }) rfl) <|
  .cons (.blockStart .toolCall) <|
  .cons (.delta 3 (.toolCall {
    id := "call-b", name := some "sum", argumentsDelta := "{\"xs\":["
  }) rfl) <|
  .cons (.delta 2 (.toolCall {
    id := "call-a", name := none, argumentsDelta := "\"lean\"}"
  }) rfl) <|
  .cons (.delta 3 (.toolCall {
    id := "call-b", name := none, argumentsDelta := "1,2]}"
  }) rfl) <|
  .cons (.delta 1 (.reasoning " check") rfl) <|
  .cons (.delta 0 (.text "world") rfl) <|
  .cons (.blockEnd 3 (.toolCall "call-b" "sum" "{\"xs\":[1,2]}") rfl) <|
  .cons (.blockEnd 0 (.text "Hello world") rfl) <|
  .cons (.blockEnd 2 (.toolCall "call-a" "lookup" "{\"q\":\"lean\"}") rfl) <|
  .cons (.blockEnd 1 (.reasoning "plan: check") rfl) <|
  .cons (.usage interleavedUsage) <|
  .cons (.finish .stop (some interleavedReplay) (by decide)) .nil

/-- The example is itself a `ValidatedTrace`, with exact raw erasure evidence. -/
def validatedInterleavedTrace : ValidatedTrace State.initial interleavedRaw := {
  finish := .terminal interleavedBlocks interleavedUsage .stop (some interleavedReplay)
  trace := interleavedTrace
  erase_eq := by decide
}

/-- The executable validator returns the same proof-carrying witness for the rich example. -/
theorem validate_interleaved_exact :
    validateTrace State.initial interleavedRaw = .ok validatedInterleavedTrace := by
  rfl

/-- Runtime replay reaches the exact endpoint carried by the typed trace. -/
theorem replay_interleaved_exact :
    replayRaw RuntimeState.initial interleavedRaw =
      .ok (.terminal interleavedBlocks interleavedUsage .stop
        (some interleavedReplay.erase)) := by
  rw [← validatedInterleavedTrace.erase_eq]
  simpa [RuntimeState.initial, State.initial, validatedInterleavedTrace] using
    (replayRaw_eraseTrace validatedInterleavedTrace.trace)

/-- First-seen slot order is retained despite out-of-order block-end events. -/
theorem interleaved_firstSeenOrder :
    interleavedBlocks = [
      .text "Hello world",
      .reasoning "plan: check",
      .toolCall "call-a" "lookup" "{\"q\":\"lean\"}",
      .toolCall "call-b" "sum" "{\"xs\":[1,2]}"
    ] :=
  rfl

/-- Raw JSON argument fragments are concatenated byte-for-byte at the `String` level. -/
theorem interleaved_rawArgumentsExact :
    (interleavedBlocks[2]?).map (fun block =>
      match block with
      | .toolCall _ _ rawArguments => rawArguments
      | _ => "") = some "{\"q\":\"lean\"}" :=
  rfl

/-- The replay envelope has exactly one optional metadata entry per retained block. -/
theorem interleaved_metadataAligned :
    interleavedReplay.perBlock.entries.length = interleavedBlocks.length :=
  interleavedReplay.perBlock.length_eq

/-! ## Exact negative examples -/

/-- A delta for an unallocated index fails closed. -/
theorem reject_missingIndex :
    applyRaw RuntimeState.initial (.textDelta 0 "orphan") =
      .error (.missingIndex 0) :=
  rfl

/-- A typed text delta cannot target a reasoning accumulator at the raw boundary. -/
theorem reject_deltaKindMismatch :
    applyRaw (.active [.open .reasoning ""] none) (.textDelta 0 "wrong") =
      .error (.deltaKindMismatch 0 .reasoning .text) :=
  rfl

/-- Deltas cannot reopen a slot after its exact block-end event. -/
theorem reject_closedIndex :
    applyRaw (.active [.closed (.text "done")] none) (.textDelta 0 "late") =
      .error (.closedIndex 0) :=
  rfl

/-- First-seen block indices must be exactly contiguous. -/
theorem reject_noncontiguousStart :
    applyRaw RuntimeState.initial (.blockStart 1 .text) =
      .error (.wrongStartIndex 0 1) :=
  rfl

/-- Duplicate usage cannot overwrite the unique accounting record. -/
theorem reject_duplicateUsage :
    applyRaw (.active [] (some interleavedUsage)) (.usage interleavedUsage) =
      .error .duplicateUsage :=
  rfl

/-- Finish cannot discard an open block. -/
theorem reject_finishWithOpenBlock :
    applyRaw (.active [.open .text "unfinished"] (some interleavedUsage))
      (.finish .stop none) = .error (.finishWithOpenBlocks [0]) :=
  rfl

/-- Replay metadata length is checked against the final retained block count. -/
theorem reject_metadataLengthMismatch :
    applyRaw (.active [.closed (.text "done")] (some interleavedUsage))
      (.finish .stop (some { responseId := none, perBlock := [none, none] })) =
        .error (.metadataLengthMismatch 1 2) :=
  rfl

/-- The proof-producing validator reports the same exact replay-alignment rejection. -/
theorem validate_reject_metadataLengthMismatch :
    validateChunk (.active [.closed (.text "done")] (some interleavedUsage))
      (.finish .stop (some { responseId := none, perBlock := [none, none] })) =
        .error (.metadataLengthMismatch 1 2) :=
  rfl

/-- The exact assembled block carried by block-end is checked, rather than trusted. -/
theorem reject_inexactBlockEnd :
    applyRaw (.active [.open .text "exact"] none)
      (.blockEnd 0 (.text "different")) =
        .error (.blockEndMismatch 0 (.text "exact") (.text "different")) :=
  rfl

/-- Error finishes are terminal just like successful finishes. -/
theorem reject_afterErrorFinish :
    let failure : StructuredFailure := {
      code := "provider_error", message := "failed", retryable := false
    }
    applyRaw (.terminal [] interleavedUsage (.error failure) none) (.textDelta 0 "late") =
      .error (.postFinish (.textDelta 0 "late")) :=
  rfl

/-- Abort finishes are terminal just like successful finishes. -/
theorem reject_afterAbortFinish :
    let cause : AbortCause := { kind := .callerCancelled, detail := "cancelled" }
    applyRaw (.terminal [] interleavedUsage (.aborted cause) none) (.finish .stop none) =
      .error (.postFinish (.finish .stop none)) :=
  rfl

end Cordis.RichStream
