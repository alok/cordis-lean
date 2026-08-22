import Cordis.DeepSeekHarnessEventProcessTimeout

/-!
# Timed process prefixes into proof-carrying session sequences

`DeepSeekHarnessEventProcessTimeout` already proves that a real configured child can be stopped
at a blocked stdout read while retaining the accepted current-Harness cursor prefix.  This module
connects that cursor directly to the existing intrinsic `SessionRefinement.ValidatedSequence`.
The conversion uses the per-entry `RefinedEvent` proofs already stored by the cursor; it does not
reparse the observed lines or invent a second semantic validation path.

The result is still a local configured-process boundary.  It does not claim JSONL byte framing,
arbitrary descendant cleanup, provider or executable authenticity, persistence, crash recovery,
or equivalence to a deployed Harness session runner.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventPrefix

open Cordis
open Cordis.SessionRefinement

/-! ## Snoc-to-cons sequence transport -/

noncomputable def ValidatedSequence.append
    {seed middle final : State} {leftEvents rightEvents : List WireEvent} :
    ValidatedSequence seed leftEvents middle →
      ValidatedSequence middle rightEvents final →
      ValidatedSequence seed (leftEvents ++ rightEvents) final
  | .nil _, right => right
  | .cons head tail, right => .cons head (append tail right)

noncomputable def PrefixSequence.toValidated
    {seed final : State} {events : List WireEvent}
    (sequence : PrefixSequence seed events final) :
    ValidatedSequence seed events final :=
  PrefixSequence.rec (motive := fun events final _ => ValidatedSequence seed events final)
    (.nil seed)
    (fun _ step ih => ValidatedSequence.append ih (.cons step (.nil _))) sequence

/-- A validated session sequence retaining the exact cursor entry ledger. -/
structure PrefixValidatedLog (cursor : Cursor) where
  entries : List EventEntry
  entries_eq : entries = cursor.entries
  events : List WireEvent
  events_eq : events = entries.map EventEntry.wire
  final : State
  final_eq : final = cursor.final
  sequence : ValidatedSequence State.initial events final

/-- Convert the cursor's snoc sequence to the validator's cons sequence. -/
noncomputable def Cursor.validatedLog (cursor : Cursor) : PrefixValidatedLog cursor where
  entries := cursor.entries
  entries_eq := rfl
  events := cursor.entries.map EventEntry.wire
  events_eq := rfl
  final := cursor.final
  final_eq := rfl
  sequence := cursor.sequence.toValidated

namespace PrefixValidatedLog

theorem final_eq_cursor (cursor : Cursor) (log : PrefixValidatedLog cursor) :
    log.final = cursor.final :=
  log.final_eq

theorem events_eq_cursor (cursor : Cursor) (log : PrefixValidatedLog cursor) :
    log.events = cursor.entries.map EventEntry.wire := by
  rw [log.events_eq, log.entries_eq]

theorem entries_length_eq_cursor (cursor : Cursor) (log : PrefixValidatedLog cursor) :
    log.entries.length = cursor.entries.length := by
  rw [log.entries_eq]

theorem projection_exact (cursor : Cursor) (log : PrefixValidatedLog cursor) :
    Session.protocolProjection log.final.session.events =
      log.sequence.protocolTrace.erase := by
  rw [log.sequence.sessionProjection_eq]
  simp [State.initial, Session.Session.empty, Session.protocolProjection]
  exact log.sequence.protocolTrace_erase.symm

end PrefixValidatedLog

end Cordis.DeepSeekHarnessEventPrefix

namespace Cordis.DeepSeekHarnessEventProcessTimeoutRefinement

open Cordis
open Cordis.DeepSeekHarnessEventPrefix
open Cordis.DeepSeekHarnessEventProcessPrefix
open Cordis.DeepSeekHarnessEventProcessTimeout

universe u

variable {policy : EntryPolicy}

/-! ## Timed process/session result -/

structure TimedPrefixValidatedResult (policy : EntryPolicy) where
  process : TimedProcessPrefixResult policy
  validated : PrefixValidatedLog process.cursor

namespace TimedPrefixValidatedResult

theorem consumed_eq_entries (result : TimedPrefixValidatedResult policy) :
    result.validated.entries.length = result.process.consumed := by
  rw [result.validated.entries_length_eq_cursor result.process.cursor]
  exact result.process.consumed_eq_entries

theorem final_eq_cursor (result : TimedPrefixValidatedResult policy) :
    result.validated.final = result.process.cursor.final :=
  result.validated.final_eq

theorem timeout_entry_eq_consumed
    (result : TimedPrefixValidatedResult policy)
    {entry : Nat} {timeoutMs : UInt32}
    (stop_eq : result.process.stop = .timedOut entry timeoutMs) :
    entry = result.process.consumed :=
  result.process.timeout_entry_eq_consumed stop_eq

theorem session_projection_eq_trace (result : TimedPrefixValidatedResult policy) :
    Session.protocolProjection result.validated.final.session.events =
      result.validated.sequence.protocolTrace.erase :=
  result.validated.projection_exact result.process.cursor

end TimedPrefixValidatedResult

/-- Run the real timer-backed process prefix and attach its intrinsic session sequence. -/
noncomputable def executeAndValidateWithTimeout
    (policy : EntryPolicy)
    (maxReads : Nat)
    (timeoutMs : UInt32)
    (config : EventProcessConfig) :
    IO (Except ProcessPrefixError (TimedPrefixValidatedResult policy)) := do
  match ← executeWithTimeout policy maxReads timeoutMs config with
  | .error error => pure (.error error)
  | .ok process =>
      pure <| .ok {
        process
        validated := process.cursor.validatedLog
      }

noncomputable def blockedSessionProcessRun :
    IO (Except ProcessPrefixError (TimedPrefixValidatedResult EntryPolicy.never)) :=
  executeAndValidateWithTimeout EntryPolicy.never 32 100 blockedReadProcess

noncomputable def delayedSessionProcessRun :
    IO (Except ProcessPrefixError (TimedPrefixValidatedResult EntryPolicy.never)) :=
  executeAndValidateWithTimeout EntryPolicy.never 32 100 delayedToolProcess

noncomputable def fastSessionProcessRun :
    IO (Except ProcessPrefixError (TimedPrefixValidatedResult EntryPolicy.never)) :=
  executeAndValidateWithTimeout EntryPolicy.never 32 2000 toolEventProcess

namespace Example

theorem blocked_timeout_entry_eq_consumed
    (result : TimedPrefixValidatedResult EntryPolicy.never)
    (stop_eq : result.process.stop = .timedOut 0 100) :
    result.process.consumed = 0 := by
  have entry := result.timeout_entry_eq_consumed stop_eq
  exact entry.symm.trans (by decide)

theorem blocked_empty_projection
    (result : TimedPrefixValidatedResult EntryPolicy.never)
    (entries_empty : result.validated.entries = []) :
    result.validated.events = [] := by
  calc
    result.validated.events = result.validated.entries.map EventEntry.wire :=
      result.validated.events_eq
    _ = [].map EventEntry.wire := by rw [entries_empty]
    _ = [] := rfl

end Example

end Cordis.DeepSeekHarnessEventProcessTimeoutRefinement
