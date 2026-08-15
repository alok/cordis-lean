import Std

/-!
# Bounded typed assistant streams

This module models an in-memory assistant text stream with an explicit chunk
budget. Typed transitions consume that budget and can finish only an open
stream, so emitting text after finish and finishing twice are unrepresentable.

The runtime mirror validates untrusted `RawChunk` values and reconstructs the
same terminal result. Tool-call payload parsing, byte-to-text decoding, network
transport, cancellation, and external persistence remain outside this pure
`String`-level model.
-/

namespace Cordis.Stream

/-- The terminal value reconstructed from a completed assistant stream. -/
structure Result where
  text : String
deriving BEq, DecidableEq, Repr

/-- An open stream retains its remaining chunk budget and exact text accumulator. -/
inductive State where
  | open (remaining : Nat) (text : String)
  | finished (result : Result)
deriving DecidableEq, Repr

namespace State

/-- Start an empty assistant stream with a fixed maximum number of text chunks. -/
def initial (budget : Nat) : State :=
  .open budget ""

end State

/--
A legal stream transition. A text chunk consumes one unit of budget, while
finish reconstructs the terminal result from the exact open accumulator.
-/
inductive Chunk : State -> State -> Type where
  | text {remaining : Nat} {accumulator : String} (fragment : String) :
      Chunk (.open (Nat.succ remaining) accumulator)
        (.open remaining (accumulator ++ fragment))
  | finish {remaining : Nat} {text : String} :
      Chunk (.open remaining text) (.finished { text := text })

/-- A compositional stream whose adjacent indexed states agree by construction. -/
inductive Trace : State -> State -> Type where
  | nil {state : State} : Trace state state
  | cons {start middle finish : State} :
      Chunk start middle -> Trace middle finish -> Trace start finish

namespace Trace

/-- Compose typed stream traces at their shared state. -/
def append {start middle finish : State} :
    Trace start middle -> Trace middle finish -> Trace start finish
  | .nil, suffix => suffix
  | .cons chunk rest, suffix => .cons chunk (append rest suffix)

/-- Regard one legal chunk as a typed trace. -/
def single {start finish : State} (chunk : Chunk start finish) : Trace start finish :=
  .cons chunk .nil

end Trace

/-- No typed chunk can be emitted after a stream has reached a terminal result. -/
theorem noChunkAfterFinished
    {result : Result}
    {finish : State}
    (chunk : Chunk (.finished result) finish) : False := by
  cases chunk

/-- Runtime state at the untrusted streaming boundary. -/
inductive RuntimeState where
  | open (remaining : Nat) (text : String)
  | finished (result : Result)
deriving DecidableEq, Repr

namespace RuntimeState

/-- Runtime counterpart of `State.initial`. -/
def initial (budget : Nat) : RuntimeState :=
  .open budget ""

end RuntimeState

/-- Untrusted text and finish messages received by the pure stream validator. -/
inductive RawChunk where
  | text (fragment : String)
  | finish
deriving BEq, DecidableEq, Repr

/-- Structured reasons why a raw chunk cannot extend the current stream. -/
inductive ValidationError where
  | budgetExhausted
  | alreadyFinished (chunk : RawChunk)
deriving BEq, DecidableEq, Repr

/-- Forget a typed stream state's indices while retaining all runtime data. -/
def eraseState : State -> RuntimeState
  | .open remaining text => .open remaining text
  | .finished result => .finished result

namespace Chunk

/-- Forget the index proof carried by a legal typed chunk. -/
def erase {start finish : State} : Chunk start finish -> RawChunk
  | .text fragment => .text fragment
  | .finish => .finish

end Chunk

namespace Trace

/-- Erase a typed trace to the raw chunk list consumed by the runtime validator. -/
def erase {start finish : State} : Trace start finish -> List RawChunk
  | .nil => []
  | .cons chunk rest => chunk.erase :: rest.erase

end Trace

/-- Validate and apply one raw chunk. -/
def applyRaw (state : RuntimeState) (chunk : RawChunk) :
    Except ValidationError RuntimeState :=
  match chunk with
  | .text fragment =>
      match state with
      | .open 0 _ => .error .budgetExhausted
      | .open (Nat.succ remaining) accumulator =>
          .ok (.open remaining (accumulator ++ fragment))
      | .finished _ => .error (.alreadyFinished (.text fragment))
  | .finish =>
      match state with
      | .open _ text => .ok (.finished { text := text })
      | .finished _ => .error (.alreadyFinished .finish)

/-- Validate and replay a finite raw chunk list from left to right. -/
def replayRaw : RuntimeState -> List RawChunk -> Except ValidationError RuntimeState
  | state, [] => .ok state
  | state, chunk :: rest => do
      let next <- applyRaw state chunk
      replayRaw next rest

/-- Applying a typed chunk after erasure reaches its statically known successor. -/
@[simp] theorem applyRaw_eraseChunk
    {start finish : State}
    (chunk : Chunk start finish) :
    applyRaw (eraseState start) chunk.erase = .ok (eraseState finish) := by
  cases chunk <;> rfl

/-- Every erased typed trace replays to its statically known terminal state. -/
@[simp] theorem replayRaw_eraseTrace
    {start finish : State}
    (trace : Trace start finish) :
    replayRaw (eraseState start) trace.erase = .ok (eraseState finish) := by
  induction trace with
  | nil => rfl
  | cons chunk rest inductionHypothesis =>
      rw [Trace.erase, replayRaw, applyRaw_eraseChunk]
      exact inductionHypothesis

/-- A raw text chunk consumes exactly one budget unit and appends exactly its fragment. -/
theorem applyRaw_text
    (remaining : Nat)
    (accumulator fragment : String) :
    applyRaw (.open (Nat.succ remaining) accumulator) (.text fragment) =
      .ok (.open remaining (accumulator ++ fragment)) :=
  rfl

/-- A raw text chunk is rejected when no chunk budget remains. -/
theorem applyRaw_budgetExhausted
    (accumulator fragment : String) :
    applyRaw (.open 0 accumulator) (.text fragment) = .error .budgetExhausted :=
  rfl

/-- A raw finish reconstructs exactly the accumulator visible in the open state. -/
theorem applyRaw_finish
    (remaining : Nat)
    (text : String) :
    applyRaw (.open remaining text) .finish = .ok (.finished { text := text }) :=
  rfl

/-- Runtime validation rejects text after a terminal result. -/
theorem applyRaw_text_after_finish
    (result : Result)
    (fragment : String) :
    applyRaw (.finished result) (.text fragment) =
      .error (.alreadyFinished (.text fragment)) :=
  rfl

/-- Runtime validation rejects a second finish message. -/
theorem applyRaw_double_finish
    (result : Result) :
    applyRaw (.finished result) .finish = .error (.alreadyFinished .finish) :=
  rfl

/-- Left-to-right concatenation used by the deterministic stream constructor. -/
def assemble (chunks : List String) : String :=
  chunks.foldl (fun text fragment => text ++ fragment) ""

/-- Build the text portion of a trace from an arbitrary current accumulator. -/
private def appendTrace (accumulator : String) : (chunks : List String) ->
    Trace (.open chunks.length accumulator)
      (.open 0 (chunks.foldl (fun text fragment => text ++ fragment) accumulator))
  | [] => .nil
  | fragment :: rest =>
      .cons (.text fragment) (appendTrace (accumulator ++ fragment) rest)

/--
Construct a typed trace for a list of fragments. The initial budget is exactly
the list length, and the terminal open accumulator is definitionally
`assemble chunks`.
-/
def textTrace (chunks : List String) :
    Trace (.open chunks.length "") (.open 0 (assemble chunks)) :=
  appendTrace "" chunks

/-- Replaying the deterministic text trace yields exactly its concatenation. -/
theorem replay_textTrace (chunks : List String) :
    replayRaw (.open chunks.length "") (textTrace chunks).erase =
      .ok (.open 0 (assemble chunks)) :=
  replayRaw_eraseTrace (textTrace chunks)

/-- Finish the deterministic text trace and reconstruct its exact assembled result. -/
def completeTrace (chunks : List String) :
    Trace (.open chunks.length "") (.finished { text := assemble chunks }) :=
  (textTrace chunks).append (.single .finish)

/--
Erasing and replaying the complete typed trace reconstructs exactly the
left-to-right concatenation of its source fragments.
-/
theorem replay_completeTrace (chunks : List String) :
    replayRaw (.open chunks.length "") (completeTrace chunks).erase =
      .ok (.finished { text := assemble chunks }) :=
  replayRaw_eraseTrace (completeTrace chunks)

end Cordis.Stream
