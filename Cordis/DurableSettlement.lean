import Cordis.Effect

/-!
# Proof-carrying durable settlement

This module adds the smallest useful durability boundary to the pure runner: an append-only
commit log whose frames contain a sequence number, a previous transcript digest, the committed
entry, the encoded successor, and the new transcript digest.  The digest is deliberately a
collision-free Lean list transcript rather than a cryptographic hash.  A `Log` is intrinsically
well formed, so every prefix selected by a `CrashPrefix` has an exact replay endpoint and an
inverse that recovers the initial state; `resume` appends after that recovered prefix.

The model covers torn-log-prefix recovery, not a filesystem, fsync, a cryptographic checksum,
multi-process exclusion, or a claim that an external side effect occurred exactly once.  Those
remain explicit adapter obligations.
-/

namespace Cordis.DurableSettlement

open Cordis

universe u v

set_option autoImplicit false

/-- A collision-free in-memory transcript used as a durable-frame digest. -/
abbrev Digest := List Nat

/-- The pure state-transition and injective encoding obligations for a durable log. -/
structure Spec (State : Type u) (Entry : Type v) where
  effect : Entry → Effect State
  entryCode : Entry → Nat
  stateCode : State → Nat
  entryCode_injective : Function.Injective entryCode
  stateCode_injective : Function.Injective stateCode
  genesis : Nat

namespace Spec

variable {State : Type u} {Entry : Type v}

def genesisDigest (spec : Spec State Entry) : Digest := [spec.genesis]

def frameDigest
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (afterCode : Nat) : Digest :=
  previous ++ [sequence, spec.entryCode entry, afterCode]

def after (spec : Spec State Entry) (entry : Entry) (before : State) : State :=
  (spec.effect entry before).after

theorem after_eq (spec : Spec State Entry) (entry : Entry) (before : State) :
    spec.after entry before = (spec.effect entry before).after := rfl

end Spec

/-- The raw, serializable shape of one commit frame. -/
structure Frame (Entry : Type v) where
  sequence : Nat
  previous : Digest
  entry : Entry
  afterCode : Nat
  digest : Digest

namespace Frame

variable {State : Type u} {Entry : Type v}

/-- Construct the exact frame emitted by a typed commit. -/
def expected
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (before : State) : Frame Entry :=
  let after := spec.after entry before
  { sequence := sequence
    previous := previous
    entry := entry
    afterCode := spec.stateCode after
    digest := spec.frameDigest previous sequence entry (spec.stateCode after) }

theorem expected_sequence
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (before : State) :
    (expected spec previous sequence entry before).sequence = sequence := rfl

theorem expected_previous
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (before : State) :
    (expected spec previous sequence entry before).previous = previous := rfl

theorem expected_afterCode
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (before : State) :
    (expected spec previous sequence entry before).afterCode =
      spec.stateCode (spec.after entry before) := rfl

theorem expected_digest
    (spec : Spec State Entry) (previous : Digest) (sequence : Nat)
    (entry : Entry) (before : State) :
    (expected spec previous sequence entry before).digest =
      spec.frameDigest previous sequence entry
        (spec.stateCode (spec.after entry before)) := rfl

end Frame

/-- A commit log indexed by its exact initial state, current state, sequence, and digest. -/
inductive Log
    {State : Type u} {Entry : Type v}
    (spec : Spec State Entry) (initial : State) :
    (current : State) → (nextSequence : Nat) → (digest : Digest) → Type (max u v) where
  | empty : Log spec initial initial 0 (spec.genesisDigest)
  | append
      {before : State} {nextSequence : Nat} {digest : Digest}
      (tail : Log spec initial before nextSequence digest) (entry : Entry) :
      Log spec initial
        (spec.after entry before)
        (nextSequence + 1)
        (spec.frameDigest digest nextSequence entry
          (spec.stateCode (spec.after entry before)))

namespace Log

variable {State : Type u} {Entry : Type v}
variable {spec : Spec State Entry} {initial current : State}
variable {nextSequence : Nat} {digest : Digest}

/-- The entries in chronological order. -/
def entries
    (spec : Spec State Entry) (initial : State) {current : State} {nextSequence : Nat}
    {digest : Digest} : Log spec initial current nextSequence digest → List Entry
  | .empty => []
  | .append tail entry => tail.entries spec initial ++ [entry]

/-- The raw frames in chronological order. -/
def frames
    (spec : Spec State Entry) (initial : State) {current : State} {nextSequence : Nat}
    {digest : Digest} : Log spec initial current nextSequence digest → List (Frame Entry)
  | .empty => []
  | @append _ _ _ _ before nextSequence digest tail entry =>
      tail.frames spec initial ++
        [Frame.expected spec digest nextSequence entry before]

/-- The newest-first inverse stack represented by the log. -/
def accumulatedUndo
    (spec : Spec State Entry) (initial : State) {current : State} {nextSequence : Nat}
    {digest : Digest} : Log spec initial current nextSequence digest → State → State
  | .empty => id
  | @append _ _ _ _ before nextSequence digest tail entry =>
      fun state =>
        tail.accumulatedUndo spec initial
          ((spec.effect entry before).undo state)

theorem entries_length
    (log : Log spec initial current nextSequence digest) :
    (log.entries spec initial).length = nextSequence := by
  induction log with
  | empty => rfl
  | @append before nextSequence digest tail entry inductionHypothesis =>
      simp only [entries, List.length_append, List.length_singleton]
      omega

theorem frames_length
    (log : Log spec initial current nextSequence digest) :
    (log.frames spec initial).length = nextSequence := by
  induction log with
  | empty => simp [frames]
  | @append before nextSequence digest tail entry inductionHypothesis =>
      simp only [frames, List.length_append, List.length_singleton]
      omega

theorem entries_map_frames
    (log : Log spec initial current nextSequence digest) :
    (log.frames spec initial).map Frame.entry = log.entries spec initial := by
  induction log with
  | empty => simp [frames, entries]
  | @append before nextSequence digest tail entry inductionHypothesis =>
      simp only [frames, entries, List.map_append, List.map_singleton]
      simp [Frame.expected, inductionHypothesis]

theorem recovers
    (log : Log spec initial current nextSequence digest) :
    log.accumulatedUndo spec initial current = initial := by
  induction log with
  | empty => simp [accumulatedUndo]
  | @append before nextSequence digest tail entry inductionHypothesis =>
      change tail.accumulatedUndo spec initial
        ((spec.effect entry before).undo (spec.effect entry before).after) = initial
      rw [(spec.effect entry before).undo_after]
      exact inductionHypothesis

theorem append_recovers
    (log : Log spec initial current nextSequence digest) (entry : Entry) :
    (Log.append log entry).accumulatedUndo spec initial
      (spec.after entry current) = initial := by
  exact (Log.append log entry).recovers

theorem frames_tail_is_expected
    (log : Log spec initial current nextSequence digest) (entry : Entry) :
    (Log.append log entry).frames spec initial =
      log.frames spec initial ++
        [Frame.expected spec digest nextSequence entry current] := by
  simp [frames]

end Log

/-- A typed crash cut: the retained prefix is a genuine indexed log and the rest is discarded. -/
structure CrashPrefix
    {State : Type u} {Entry : Type v}
    (spec : Spec State Entry) (initial : State)
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    (source : Log spec initial sourceCurrent sourceSequence sourceDigest) where
  retainedCurrent : State
  retainedSequence : Nat
  retainedDigest : Digest
  retained : Log spec initial retainedCurrent retainedSequence retainedDigest
  discarded : List (Frame Entry)
  frames_split : source.frames spec initial =
    retained.frames spec initial ++ discarded

namespace CrashPrefix

variable {State : Type u} {Entry : Type v}
variable {spec : Spec State Entry} {initial : State}

def recoveredState
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    {source : Log spec initial sourceCurrent sourceSequence sourceDigest}
    (cut : CrashPrefix spec initial source) : State :=
  cut.retainedCurrent

theorem recovers_initial
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    {source : Log spec initial sourceCurrent sourceSequence sourceDigest}
    (cut : CrashPrefix spec initial source) :
    cut.retained.accumulatedUndo spec initial cut.retainedCurrent = initial :=
  cut.retained.recovers

theorem retained_frames_are_prefix
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    {source : Log spec initial sourceCurrent sourceSequence sourceDigest}
    (cut : CrashPrefix spec initial source) :
    source.frames spec initial =
      cut.retained.frames spec initial ++ cut.discarded :=
  cut.frames_split

/-- Resume after the retained prefix by committing one new entry. -/
def resume
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    {source : Log spec initial sourceCurrent sourceSequence sourceDigest}
    (cut : CrashPrefix spec initial source) (entry : Entry) :
    Log spec initial
      (spec.after entry cut.retainedCurrent)
      (cut.retainedSequence + 1)
      (spec.frameDigest cut.retainedDigest cut.retainedSequence entry
        (spec.stateCode (spec.after entry cut.retainedCurrent))) :=
  .append cut.retained entry

theorem resume_recovers
    {sourceCurrent : State} {sourceSequence : Nat} {sourceDigest : Digest}
    {source : Log spec initial sourceCurrent sourceSequence sourceDigest}
    (cut : CrashPrefix spec initial source) (entry : Entry) :
    (cut.resume entry).accumulatedUndo spec initial
      (spec.after entry cut.retainedCurrent) = initial := by
  exact (cut.resume entry).recovers

end CrashPrefix

/-- A crash cut with no discarded frames is the identity recovery certificate. -/
def identityCrashPrefix
    {State : Type u} {Entry : Type v}
    {spec : Spec State Entry} {initial current : State}
    {nextSequence : Nat} {digest : Digest}
    (log : Log spec initial current nextSequence digest) :
    CrashPrefix spec initial log where
  retainedCurrent := current
  retainedSequence := nextSequence
  retainedDigest := digest
  retained := log
  discarded := []
  frames_split := by simp

/-! ## A concrete executable settlement example -/

namespace Example

def entryEffect (amount : Nat) : Effect Nat := fun before =>
  { after := before + amount
    undo := fun current => current - amount
    undo_after := by omega }

def spec : Spec Nat Nat where
  effect := entryEffect
  entryCode := id
  stateCode := id
  entryCode_injective := by intro left right equality; exact equality
  stateCode_injective := by intro left right equality; exact equality
  genesis := 17

def initial : Nat := 10

def first : Log spec initial
    (spec.after 3 initial) 1
    (spec.frameDigest (spec.genesisDigest) 0 3
      (spec.stateCode (spec.after 3 initial))) :=
  .append .empty 3

def second : Log spec initial
    (spec.after 8 (spec.after 3 initial)) 2
    (spec.frameDigest
      (spec.frameDigest (spec.genesisDigest) 0 3
        (spec.stateCode (spec.after 3 initial)))
      1 8 (spec.stateCode (spec.after 8 (spec.after 3 initial)))) :=
  .append first 8

def crash : CrashPrefix spec initial second where
  retainedCurrent := spec.after 3 initial
  retainedSequence := 1
  retainedDigest := spec.frameDigest (spec.genesisDigest) 0 3
    (spec.stateCode (spec.after 3 initial))
  retained := first
  discarded := [Frame.expected spec
    (spec.frameDigest (spec.genesisDigest) 0 3
      (spec.stateCode (spec.after 3 initial)))
    1 8 (spec.after 3 initial)]
  frames_split := by simp [second, first, Log.frames, Frame.expected]

theorem first_after : spec.after 3 initial = 13 := rfl

theorem second_after : spec.after 8 (spec.after 3 initial) = 21 := rfl

theorem second_recovers :
    second.accumulatedUndo spec initial (spec.after 8 (spec.after 3 initial)) = initial := by
  exact second.recovers

theorem crash_recovers :
    crash.retained.accumulatedUndo spec initial crash.retainedCurrent = initial := by
  exact crash.recovers_initial

def resumed : Log spec initial
    (spec.after 5 (spec.after 3 initial)) 2
    (spec.frameDigest
      (spec.frameDigest (spec.genesisDigest) 0 3
        (spec.stateCode (spec.after 3 initial)))
      1 5 (spec.stateCode (spec.after 5 (spec.after 3 initial)))) :=
  crash.resume 5

theorem resumed_after : spec.after 5 (spec.after 3 initial) = 18 := rfl

theorem resumed_recovers :
    resumed.accumulatedUndo spec initial (spec.after 5 13) = initial := by
  exact resumed.recovers

theorem crash_drops_uncommitted_tail :
    crash.discarded.length = 1 := by rfl

end Example

end Cordis.DurableSettlement
