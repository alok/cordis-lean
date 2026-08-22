import Cordis.SessionRefinement
import Cordis.TextRefinement

/-!
# Incremental current-Harness event prefix

`SessionRefinement.validateJsonLog` proves a complete supported JSON-AST log.  This
module exposes the same refinement as an append-only dependent cursor: each accepted
JSON object is decoded, jointly validated by the Session and Protocol validators, and
snoc'ed onto an intrinsic prefix trace whose endpoint is the cursor's new state.

The cursor is intentionally independent of IO.  It is the stateful target that a
future file/process reader can feed one framed JSON object at a time; this module does
not claim JSONL framing, blocked-read interruption, crash durability, provider
authenticity, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventPrefix

open Cordis
open Cordis.SessionRefinement
open Cordis.TextRefinement

inductive PrefixError where
  | decode (error : DecodeError)
  | refine (error : RefinementError)
deriving DecidableEq, Repr

/-- One raw JSON object and the exact wire event obtained from it. -/
structure EventEntry where
  raw : Lean.Json
  wire : WireEvent
  decoded : decodeEvent raw = .ok wire

/-- A snoc-shaped accepted sequence, convenient for an append-only cursor. -/
inductive PrefixSequence : State → List WireEvent → State → Type where
  | nil (state : State) : PrefixSequence state [] state
  | snoc {seed middle : State} {events : List WireEvent} {wire : WireEvent}
      (prior : PrefixSequence seed events middle)
      (step : RefinedEvent middle wire) :
      PrefixSequence seed (events ++ [wire]) step.after

namespace PrefixSequence

def protocolTrace {seed final : State} {events : List WireEvent} :
    PrefixSequence seed events final → Cordis.Trace seed.protocol final.protocol
  | .nil _ => .nil
  | .snoc prior step =>
      prior.protocolTrace.append
        (ProtocolDelta.prependTrace step.protocol .nil)

def runtimeEvents {seed final : State} {events : List WireEvent} :
    PrefixSequence seed events final → List RuntimeEvent
  | .nil _ => []
  | .snoc prior step => prior.runtimeEvents ++ step.candidate.runtime.toList

theorem protocolTrace_erase {seed final : State} {events : List WireEvent}
    (sequence : PrefixSequence seed events final) :
    sequence.protocolTrace.erase = sequence.runtimeEvents := by
  induction sequence with
  | nil => rfl
  | snoc prior step inductionHypothesis =>
      change (prior.protocolTrace.append
        (ProtocolDelta.prependTrace step.protocol .nil)).erase =
        prior.runtimeEvents ++ step.candidate.runtime.toList
      rw [Cordis.Trace.erase_append, inductionHypothesis,
        ProtocolDelta.prependTrace_erase]
      simp [Cordis.Trace.erase]

theorem sessionProjection_eq {seed final : State} {events : List WireEvent}
    (sequence : PrefixSequence seed events final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection seed.session.events ++ sequence.runtimeEvents := by
  induction sequence with
  | nil => simp [runtimeEvents]
  | snoc prior step inductionHypothesis =>
      change Session.protocolProjection step.after.session.events =
        Session.protocolProjection _ ++
          (prior.runtimeEvents ++ step.candidate.runtime.toList)
      rw [step.protocolProjection_eq, inductionHypothesis]
      simp [List.append_assoc]

end PrefixSequence

/-- The complete accepted cursor state, including every raw JSON entry. -/
structure Cursor where
  entries : List EventEntry
  final : State
  sequence : PrefixSequence State.initial (entries.map EventEntry.wire) final

namespace Cursor

def initial : Cursor where
  entries := []
  final := State.initial
  sequence := .nil State.initial

def pushDecoded (cursor : Cursor) (raw : Lean.Json) (wire : WireEvent)
    (decoded : decodeEvent raw = .ok wire)
    (step : RefinedEvent cursor.final wire) : Cursor :=
  let entry : EventEntry := { raw := raw, wire := wire, decoded := decoded }
  {
    entries := cursor.entries ++ [entry]
    final := step.after
    sequence := by
      simpa [entry, List.map_append] using PrefixSequence.snoc cursor.sequence step
  }

def push (cursor : Cursor) (raw : Lean.Json) : Except PrefixError Cursor :=
  match decoded : decodeEvent raw with
  | .error error => .error (.decode error)
  | .ok wire =>
      match _refined : refineEvent cursor.final wire with
      | .error error => .error (.refine error)
      | .ok step => .ok (pushDecoded cursor raw wire decoded step)

@[simp] theorem pushDecoded_final (cursor : Cursor) (raw : Lean.Json) (wire : WireEvent)
    (decoded : decodeEvent raw = .ok wire) (step : RefinedEvent cursor.final wire) :
    (pushDecoded cursor raw wire decoded step).final = step.after := by
  rfl

theorem pushDecoded_sessionProjection (cursor : Cursor) (raw : Lean.Json)
    (wire : WireEvent) (decoded : decodeEvent raw = .ok wire)
    (step : RefinedEvent cursor.final wire) :
    Session.protocolProjection (pushDecoded cursor raw wire decoded step).final.session.events =
      Session.protocolProjection cursor.final.session.events ++
        step.candidate.runtime.toList := by
  exact step.protocolProjection_eq

end Cursor

/-- A deterministic entry policy used to model bounded reads and cooperative stops. -/
structure EntryPolicy where
  decide : Nat → Bool
  reason : Nat → String

namespace EntryPolicy

def never : EntryPolicy where
  decide := fun _ => false
  reason := fun _ => "never"

def atEntry (entry : Nat) (message : String) : EntryPolicy where
  decide := fun current => current = entry
  reason := fun _ => message

end EntryPolicy

inductive PrefixStop (policy : EntryPolicy) where
  | completed
  | fuelExhausted
  | cancelled (entry : Nat) (reason : String)
      (decided : policy.decide entry = true)

namespace PrefixStop

def isCompleted {policy : EntryPolicy} : PrefixStop policy → Bool
  | .completed => true
  | .fuelExhausted | .cancelled .. => false

def isFuelExhausted {policy : EntryPolicy} : PrefixStop policy → Bool
  | .fuelExhausted => true
  | .completed | .cancelled .. => false

def isCancelled {policy : EntryPolicy} : PrefixStop policy → Bool
  | .cancelled .. => true
  | .completed | .fuelExhausted => false

end PrefixStop

/-- A pure prefix result.  `remaining` makes the stop point explicit. -/
structure RunResult (policy : EntryPolicy) where
  cursor : Cursor
  consumed : Nat
  remaining : List Lean.Json
  stop : PrefixStop policy

namespace RunResult

def entries {policy : EntryPolicy} (result : RunResult policy) : Nat :=
  result.cursor.entries.length

def isCompleted {policy : EntryPolicy} (result : RunResult policy) : Bool :=
  result.stop.isCompleted

def isFuelExhausted {policy : EntryPolicy} (result : RunResult policy) : Bool :=
  result.stop.isFuelExhausted

def isCancelled {policy : EntryPolicy} (result : RunResult policy) : Bool :=
  result.stop.isCancelled

end RunResult

private def runAux (policy : EntryPolicy) : Nat → Cursor → List Lean.Json → Nat →
    Except PrefixError (RunResult policy)
  | _, cursor, [], consumed =>
      .ok { cursor, consumed, remaining := [], stop := .completed }
  | 0, cursor, raws, consumed =>
      .ok { cursor, consumed, remaining := raws, stop := .fuelExhausted }
  | fuel + 1, cursor, raw :: raws, consumed =>
      if decided : policy.decide consumed then
        .ok {
          cursor
          consumed
          remaining := raw :: raws
          stop := .cancelled consumed (policy.reason consumed) decided
        }
      else
        match Cursor.push cursor raw with
        | .error error => .error error
        | .ok next => runAux policy fuel next raws (consumed + 1)

/-- Consume an in-memory JSON-object list one event at a time. -/
def run (policy : EntryPolicy) (fuel : Nat) (raws : List Lean.Json) :
    Except PrefixError (RunResult policy) :=
  runAux policy fuel Cursor.initial raws 0

/-- Parse canonical JSONL first, then feed each AST object through the cursor. -/
def runText (policy : EntryPolicy) (fuel : Nat) (source : String) :
    Except (TextError ⊕ PrefixError) (RunResult policy) :=
  match _parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok raws =>
      match run policy fuel raws with
      | .error error => .error (.inr error)
      | .ok result => .ok result

theorem run_completed_empty (policy : EntryPolicy) :
    run policy 0 [] = .ok {
      cursor := Cursor.initial
      consumed := 0
      remaining := []
      stop := .completed
    } := by
  rfl

theorem run_cancelled_before_first (fuel : Nat) (raw : Lean.Json)
    (rest : List Lean.Json) :
    run (EntryPolicy.atEntry 0 "cancelled:first") (fuel + 1) (raw :: rest) = .ok {
      cursor := Cursor.initial
      consumed := 0
      remaining := raw :: rest
      stop := .cancelled 0 "cancelled:first" (by rfl)
    } := by
  rfl

def toolTextSource : String :=
  TextRefinement.renderJsonLines SessionRefinement.toolMessageExampleJson

def toolPrefixRun :
    Except (TextError ⊕ PrefixError) (RunResult EntryPolicy.never) :=
  runText EntryPolicy.never 32 toolTextSource

end Cordis.DeepSeekHarnessEventPrefix
