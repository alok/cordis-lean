import Cordis.DeepSeekStream

/-!
# Proof-carrying incremental DeepSeek SSE prefixes

`DeepSeekStream.validateSse` checks a complete body. This module adds the missing pure prefix
boundary: a caller can feed complete SSE lines one at a time, receive a typed state after every
accepted line, stop before another line, and finally demand the terminal `[DONE]` certificate.
The parser retains the exact accumulated body, parsed frames, line count, and prefix equation.

The implementation deliberately separates prefix parsing from completion. A prefix may be valid
without `[DONE]`; `finish` still invokes the original complete-body validator, so malformed
terminal framing cannot be mistaken for a completed stream. This is not a live HTTP reader,
backpressure theorem, process cancellation, reconnect protocol, or provider-complete assembler.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamIncremental

open Cordis.DeepSeekStream

/-! ## Line-level prefix state -/

private def normalizeLine (line : String) : String :=
  if line.endsWith "\r" then (line.dropEnd 1).toString else line

private def isDoneLine (line : String) : Bool :=
  let normalized := normalizeLine line
  if normalized.startsWith "data:" then
    let payload := (normalized.drop 5).toString
    (if payload.startsWith " " then (payload.drop 1).toString else payload) = "[DONE]"
  else
    false

structure PrefixState where
  body : String
  frames : List Frame
  line : Nat
  done : Bool
  parsed : parseSsePrefix body = .ok frames

namespace PrefixState

def initial : PrefixState where
  body := ""
  frames := []
  line := 0
  done := false
  parsed := DeepSeekStream.parseSsePrefix_empty

theorem initial_body : initial.body = "" := rfl

theorem initial_frames : initial.frames = [] := rfl

theorem initial_not_done : initial.done = false := rfl

end PrefixState

def pushLine (state : PrefixState) (line : String) : Except StreamError PrefixState :=
  let nextBody := state.body ++ line ++ "\n"
  match parsed : parseSsePrefix nextBody with
  | .error error => .error error
  | .ok frames =>
      .ok {
        body := nextBody
        frames
        line := state.line + 1
        done := state.done || isDoneLine line
        parsed
      }

def finish (state : PrefixState) : Except StreamError (ValidatedSseStream state.body) :=
  match validateSse state.body with
  | .error error => .error error
  | .ok _stream => .ok _stream

/-! ## Stop policy and finite line runner -/

structure LinePolicy where
  reason : String
  decide : Nat → Bool

namespace LinePolicy

def never (reason : String := "cancelled:user") : LinePolicy where
  reason
  decide := fun _ => false

def atLine (line : Nat) (reason : String) : LinePolicy where
  reason
  decide := fun current => current = line

theorem never_decide (reason : String) (line : Nat) :
    (never reason).decide line = false := rfl

theorem atLine_decide (line target : Nat) (reason : String) :
    (atLine target reason).decide line = (line == target) := by
  rfl

end LinePolicy

inductive StreamStop (policy : LinePolicy) (state : PrefixState) where
  | completed (validated : ValidatedSseStream state.body)
  | fuelExhausted
  | cancelled
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true)

namespace StreamStop

def isCompleted {policy : LinePolicy} {state : PrefixState} :
    StreamStop policy state -> Bool
  | .completed _ => true
  | .fuelExhausted | .cancelled _ _ _ => false

def isFuelExhausted {policy : LinePolicy} {state : PrefixState} :
    StreamStop policy state -> Bool
  | .completed _ | .cancelled _ _ _ => false
  | .fuelExhausted => true

def isCancelled {policy : LinePolicy} {state : PrefixState} :
    StreamStop policy state -> Bool
  | .completed _ | .fuelExhausted => false
  | .cancelled _ _ _ => true

def cancelledLine {policy : LinePolicy} {state : PrefixState} :
    StreamStop policy state -> Option Nat
  | .completed _ | .fuelExhausted => none
  | .cancelled line _ _ => some line

def cancelledReason {policy : LinePolicy} {state : PrefixState} :
    StreamStop policy state -> Option String
  | .completed _ | .fuelExhausted => none
  | .cancelled _ reason _ => some reason

end StreamStop

structure IncrementalResult (policy : LinePolicy) where
  state : PrefixState
  stop : StreamStop policy state

private def consumeLinesAux
    (policy : LinePolicy)
    (fuel : Nat)
    (lines : List String)
    (state : PrefixState) :
    Except StreamError (IncrementalResult policy) :=
  match fuel with
  | 0 => .ok { state, stop := .fuelExhausted }
  | fuel + 1 =>
      if decided : policy.decide state.line then
        .ok { state, stop := .cancelled state.line policy.reason decided }
      else
        match lines with
        | [] =>
            match finish state with
            | .error error => .error error
            | .ok validated => .ok { state, stop := .completed validated }
        | line :: rest =>
            match pushLine state line with
            | .error error => .error error
            | .ok next => consumeLinesAux policy fuel rest next

def consumeLines (policy : LinePolicy) (fuel : Nat) (lines : List String) :
    Except StreamError (IncrementalResult policy) :=
  consumeLinesAux policy fuel lines PrefixState.initial

def consumeBody (policy : LinePolicy) (fuel : Nat) (body : String) :
    Except StreamError (IncrementalResult policy) :=
  consumeLines policy fuel (body.splitOn "\n")

end Cordis.DeepSeekStreamIncremental
