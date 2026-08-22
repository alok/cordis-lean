import Cordis.RuntimeRefinement

/-!
# Source-shaped DeepSeek provider assembler

This module is a small, proof-carrying model of the current TypeScript
`BlockAssembler` boundary at DeepSeek Harness commit
`47f943859bef60e4160492346772ded9b24f765a` (`packages/llm/llm/src/assembler.ts`).
It intentionally sits next to, rather than inside,
the stricter `DeepSeekRichMultiStream` validator: the provider assembler accepts
delta-only and open blocks, keeps the first block close, overwrites tool metadata
with the latest supplied values, keeps the last usage/finish metadata, defaults a
missing finish to `stop`, and removes tool calls for `max-tokens`.

The input vocabulary is the canonical post-decoder chunk shape, not a claim about
wire JSON or transport.  Unknown open block types are retained until assembly and
then fail with a typed error, matching the source assembler's throwing branch.
`replayState` is represented as opaque text here; no JSON schema or deployed
TypeScript behavioral equivalence is claimed.  Every successful result is returned
with a certificate that records the exact folded state and assembly equation.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProviderAssembler

open Cordis

/-! ## Canonical chunk vocabulary -/

inductive BlockType where
  | text
  | reasoning
  | toolCall
  | unknown (label : String)
  deriving BEq, DecidableEq, Repr

inductive Block where
  | text (content : String)
  | reasoning (content : String)
  | toolCall (id name arguments : String)
  deriving BEq, DecidableEq, Repr

structure Usage where
  inputTokens : Nat
  outputTokens : Nat
  cacheReadTokens : Option Nat := none
  cacheWriteTokens : Option Nat := none
  reasoningTokens : Option Nat := none
  deriving BEq, DecidableEq, Repr

structure Failure where
  code : String
  message : String
  deriving BEq, DecidableEq, Repr

inductive Finish where
  | stop
  | toolCalls
  | maxTokens
  | aborted (failure : Failure)
  | error (failure : Failure)
  deriving BEq, DecidableEq, Repr

inductive Chunk where
  | blockStart (index : Nat) (kind : BlockType)
  | textDelta (index : Nat) (fragment : String)
  | reasoningDelta (index : Nat) (fragment : String)
  | toolCallDelta (index : Nat) (id : String) (name : Option String)
      (argumentsDelta : String)
  | blockEnd (index : Nat) (block : Block)
  | usage (value : Usage)
  | finish (reason : Finish) (replayState : Option String)
  deriving BEq, DecidableEq, Repr

/-! ## Partial blocks and deterministic fold -/

structure Partial where
  kind : BlockType
  text : String := ""
  toolCallId : Option String := none
  toolCallName : Option String := none
  toolCallArguments : String := ""
  closed : Option Block := none
  deriving BEq, DecidableEq, Repr

structure Entry where
  index : Nat
  slot : Partial
  deriving BEq, DecidableEq, Repr

structure State where
  partials : List Entry := []
  order : List Nat := []
  usage : Option Usage := none
  finish : Option Finish := none
  replayState : Option String := none
  deriving BEq, DecidableEq, Repr

def initial : State := {}

private def lookupEntry : Nat → List Entry → Option Entry
  | _, [] => none
  | index, entry :: rest =>
      if entry.index = index then some entry else lookupEntry index rest

private def replaceEntry (index : Nat) (update : Partial → Partial) :
    List Entry → List Entry
  | [] => []
  | entry :: rest =>
      if entry.index = index then
        { entry with slot := update entry.slot } :: rest
      else
        entry :: replaceEntry index update rest

private def blockType : Block → BlockType
  | .text _ => .text
  | .reasoning _ => .reasoning
  | .toolCall _ _ _ => .toolCall

private def ensure (state : State) (index : Nat) (kind : BlockType) : State :=
  match lookupEntry index state.partials with
  | some _ => state
  | none =>
      let entry : Entry := {
        index
        slot := { kind }
      }
      { state with
          partials := state.partials ++ [entry]
          order := state.order ++ [index] }

private def updateOpen (state : State) (index : Nat) (kind : BlockType)
    (update : Partial → Partial) : State :=
  let ensured := ensure state index kind
  match lookupEntry index ensured.partials with
  | none => ensured
  | some entry =>
      match entry.slot.closed with
      | some _ => ensured
      | none =>
          { ensured with partials := replaceEntry index update ensured.partials }

private def close (state : State) (index : Nat) (block : Block) : State :=
  let ensured := ensure state index (blockType block)
  match lookupEntry index ensured.partials with
  | none => ensured
  | some entry =>
      match entry.slot.closed with
      | some _ => ensured
      | none =>
          { ensured with
              partials := replaceEntry index (fun slot =>
                { slot with closed := some block }) ensured.partials }

/-- One source-shaped state transition.  Closed deltas are ignored. -/
def push (state : State) : Chunk → State
  | .blockStart index kind => ensure state index kind
  | .textDelta index fragment =>
      updateOpen state index .text (fun slot =>
        { slot with text := slot.text ++ fragment })
  | .reasoningDelta index fragment =>
      updateOpen state index .reasoning (fun slot =>
        { slot with text := slot.text ++ fragment })
  | .toolCallDelta index id name argumentsDelta =>
      updateOpen state index .toolCall (fun slot =>
        { slot with
            toolCallId := some id
            toolCallName := match name with
              | some value => some value
              | none => slot.toolCallName
            toolCallArguments := slot.toolCallArguments ++ argumentsDelta })
  | .blockEnd index block => close state index block
  | .usage value => { state with usage := some value }
  | .finish reason replayState =>
      { state with finish := some reason, replayState }

def pushMany (chunks : List Chunk) : State :=
  chunks.foldl push initial

/-! ## Assembly and certificates -/

inductive AssemblyError where
  | missingIndex (index : Nat)
  | unknownBlockType (index : Nat) (label : String)
  deriving BEq, DecidableEq, Repr

structure Assembled where
  role : String
  blocks : List Block
  usage : Option Usage
  finish : Finish
  replayState : Option String
  deriving BEq, DecidableEq, Repr

private def finishOf (state : State) : Finish := state.finish.getD .stop

private def assemblePartial (index : Nat) : Partial → Except AssemblyError Block
  | { closed := some block, .. } => .ok block
  | { kind := .text, text, .. } => .ok (.text text)
  | { kind := .reasoning, text, .. } => .ok (.reasoning text)
  | { kind := .toolCall, toolCallId, toolCallName, toolCallArguments, .. } =>
      .ok (.toolCall (toolCallId.getD s!"call-{index}")
        (toolCallName.getD "") toolCallArguments)
  | { kind := .unknown label, .. } => .error (.unknownBlockType index label)

private def assembleIndices (state : State) : List Nat →
    Except AssemblyError (List Block)
  | [] => .ok []
  | index :: rest => do
      let entry ← match lookupEntry index state.partials with
        | some entry => .ok entry
        | none => .error (.missingIndex index)
      let block ← assemblePartial index entry.slot
      let suffix ← assembleIndices state rest
      .ok (block :: suffix)

private def keepBlock (finish : Finish) : Block → Bool
  | .toolCall _ _ _ => finish != .maxTokens
  | _ => true

def assemble (state : State) : Except AssemblyError Assembled := do
  let blocks ← assembleIndices state state.order
  let finish := finishOf state
  .ok {
    role := "assistant"
    blocks := blocks.filter (keepBlock finish)
    usage := state.usage
    finish
    replayState := state.replayState
  }

structure Certificate (chunks : List Chunk) where
  state : State
  state_eq : pushMany chunks = state
  result : Assembled
  result_eq : assemble state = .ok result

/-- Assemble a finite canonical chunk list while retaining both defining equations. -/
def validate (chunks : List Chunk) :
    Except AssemblyError (Certificate chunks) :=
  let state := pushMany chunks
  match result_eq : assemble state with
  | .error error => .error error
  | .ok result => .ok {
      state
      state_eq := rfl
      result
      result_eq
    }

theorem Certificate.fold_exact {chunks : List Chunk} (certificate : Certificate chunks) :
    pushMany chunks = certificate.state :=
  certificate.state_eq

theorem Certificate.assembly_exact {chunks : List Chunk} (certificate : Certificate chunks) :
    assemble certificate.state = .ok certificate.result :=
  certificate.result_eq

/-! ## Composition with the strict current-Harness JSON subset -/

private def blockKindOf : Cordis.RichStream.BlockKind → BlockType
  | .text => .text
  | .reasoning => .reasoning
  | .toolCall => .toolCall

private def blockOf : Cordis.RichStream.ContentBlock → Block
  | .text content => .text content
  | .reasoning content => .reasoning content
  | .toolCall id name arguments => .toolCall id name arguments

private def usageOf (usage : Cordis.RuntimeRefinement.WireUsage) : Usage := {
  inputTokens := usage.inputTokens.value
  outputTokens := usage.outputTokens.value
  cacheReadTokens := usage.cacheReadTokens.map (fun value => value.value)
  cacheWriteTokens := usage.cacheWriteTokens.map (fun value => value.value)
  reasoningTokens := usage.reasoningTokens.map (fun value => value.value)
}

private def finishKindOf : Cordis.RuntimeRefinement.SuccessfulFinish → Finish
  | .stop => .stop
  | .toolCalls => .toolCalls
  | .maxTokens => .maxTokens

/-- Exact map from the accepted JSON-AST chunk subset to canonical assembler chunks. -/
def fromSupported : Cordis.RuntimeRefinement.SupportedChunk → Chunk
  | .blockStart index kind => .blockStart index.value (blockKindOf kind)
  | .textDelta index text => .textDelta index.value text
  | .reasoningDelta index text => .reasoningDelta index.value text
  | .toolCallDelta index id name argumentsDelta =>
      .toolCallDelta index.value id name argumentsDelta
  | .blockEnd index block => .blockEnd index.value (blockOf block)
  | .tokenUsage usage => .usage (usageOf usage)
  | .finish reason => .finish (finishKindOf reason) none

inductive JsonAssemblyError where
  | stream (error : Cordis.RuntimeRefinement.ValidationError)
  | assembler (error : AssemblyError)
  deriving BEq, DecidableEq, Repr

structure ValidatedJsonAssembly (input : List Lean.Json) where
  stream : Cordis.RuntimeRefinement.ValidatedJsonTrace input
  assembly : Certificate (stream.chunks.map fromSupported)

/-- Compose strict JSON/rich validation with source-shaped post-decoder assembly. -/
def validateJsonAssembly (input : List Lean.Json) :
    Except JsonAssemblyError (ValidatedJsonAssembly input) :=
  match Cordis.RuntimeRefinement.validateJsonTrace input with
  | .error error => .error (.stream error)
  | .ok stream =>
      match validate (stream.chunks.map fromSupported) with
      | .error error => .error (.assembler error)
      | .ok assembly => .ok { stream, assembly }

theorem ValidatedJsonAssembly.stream_exact {input : List Lean.Json}
    (value : ValidatedJsonAssembly input) :
    Cordis.RuntimeRefinement.decodeChunks input = .ok value.stream.chunks :=
  value.stream.decode_eq

theorem ValidatedJsonAssembly.assembly_exact {input : List Lean.Json}
    (value : ValidatedJsonAssembly input) :
    assemble value.assembly.state = .ok value.assembly.result :=
  value.assembly.result_eq

def jsonExampleResult : Option Assembled :=
  match validateJsonAssembly Cordis.RuntimeRefinement.exampleJson with
  | .error _ => none
  | .ok value => some value.assembly.result

def jsonExampleExpected : Assembled := {
  role := "assistant"
  blocks := [.text "hello"]
  usage := some {
    inputTokens := 5
    outputTokens := 2
  }
  finish := .stop
  replayState := none
}

theorem json_example_assembly_exact : jsonExampleResult = some jsonExampleExpected := by
  rfl

/-! ## Exact source-shaped witnesses -/

namespace Example

def usage1 : Usage := {
  inputTokens := 4
  outputTokens := 7
  cacheReadTokens := some 1
}

def usage2 : Usage := {
  inputTokens := 8
  outputTokens := 11
  cacheReadTokens := some 2
  reasoningTokens := some 3
}

def multiToolChunks : List Chunk := [
  .blockStart 0 .text,
  .textDelta 0 "answer",
  .blockStart 1 .toolCall,
  .toolCallDelta 1 "call-a" (some "lookup") "{\"q\":",
  .toolCallDelta 1 "call-a" none "\"x\"}",
  .blockStart 2 .toolCall,
  .toolCallDelta 2 "call-b" (some "sum") "[1,2]",
  .usage usage1,
  .usage usage2,
  .finish .toolCalls (some "replay-v1")
]

def multiToolExpected : Assembled := {
  role := "assistant"
  blocks := [
    .text "answer",
    .toolCall "call-a" "lookup" "{\"q\":\"x\"}",
    .toolCall "call-b" "sum" "[1,2]"
  ]
  usage := some usage2
  finish := .toolCalls
  replayState := some "replay-v1"
}

def multiToolResult : Option Assembled :=
  match validate multiToolChunks with
  | .error _ => none
  | .ok certificate => some certificate.result

theorem multiTool_result_exact : multiToolResult = some multiToolExpected := by
  rfl

def closedFirstChunks : List Chunk := [
  .blockStart 0 .text,
  .textDelta 0 "open",
  .blockEnd 0 (.text "closed"),
  .textDelta 0 "ignored",
  .blockEnd 0 (.text "second")
]

def closedFirstExpected : Assembled := {
  role := "assistant"
  blocks := [.text "closed"]
  usage := none
  finish := .stop
  replayState := none
}

def closedFirstResult : Option Assembled :=
  match validate closedFirstChunks with
  | .error _ => none
  | .ok certificate => some certificate.result

theorem first_close_wins : closedFirstResult = some closedFirstExpected := by
  rfl

def maxTokensChunks : List Chunk := [
  .blockStart 0 .text,
  .textDelta 0 "truncated",
  .blockStart 1 .toolCall,
  .toolCallDelta 1 "call-dropped" (some "lookup") "{}",
  .blockStart 7 .toolCall,
  .usage usage1,
  .finish .maxTokens none
]

def maxTokensExpected : Assembled := {
  role := "assistant"
  blocks := [.text "truncated"]
  usage := some usage1
  finish := .maxTokens
  replayState := none
}

def maxTokensResult : Option Assembled :=
  match validate maxTokensChunks with
  | .error _ => none
  | .ok certificate => some certificate.result

theorem max_tokens_drops_tools : maxTokensResult = some maxTokensExpected := by
  rfl

def metadataLastWinsChunks : List Chunk := [
  .usage usage1,
  .usage usage2,
  .finish .stop none,
  .finish .maxTokens (some "last")
]

def metadataLastWinsExpected : Assembled := {
  role := "assistant"
  blocks := []
  usage := some usage2
  finish := .maxTokens
  replayState := some "last"
}

def metadataLastWinsResult : Option Assembled :=
  match validate metadataLastWinsChunks with
  | .error _ => none
  | .ok certificate => some certificate.result

theorem metadata_last_wins :
    metadataLastWinsResult = some metadataLastWinsExpected := by
  rfl

def unknownOpenChunks : List Chunk := [
  .blockStart 4 (.unknown "image")
]

theorem unknown_open_is_rejected :
    validate unknownOpenChunks = .error (.unknownBlockType 4 "image") := by
  rfl

def multiToolSummary : Bool :=
  match multiToolResult with
  | some result =>
      result.role = "assistant" && result.blocks.length = 3 &&
        result.finish = .toolCalls && result.usage = some usage2
  | none => false

def maxTokensSummary : Bool :=
  match maxTokensResult with
  | some result => result.blocks = [.text "truncated"] &&
      result.finish = .maxTokens
  | none => false

def metadataSummary : Bool :=
  match metadataLastWinsResult with
  | some result => result.usage = some usage2 && result.replayState = some "last"
  | none => false

theorem executable_summaries :
    multiToolSummary = true ∧ maxTokensSummary = true ∧ metadataSummary = true := by
  decide

end Example

end Cordis.DeepSeekProviderAssembler
