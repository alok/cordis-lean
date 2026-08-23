import Cordis.DeepSeekHarnessEventIgnorableNormalization

/-!
# Occurrence-indexed source-to-local Harness simulation

The archive and normalization layers certify which physical rows are retained, but an endpoint
certificate alone does not expose the semantic transition induced by each retained row.  This
module adds that missing dependent layer: every normalized occurrence is consumed by a
`RefinedEvent` indexed by the state immediately before it.  The resulting `SourceReplay` is an
intrinsic local trace, while `SourceLedger` retains the keep/drop partition.

This is a finite supported-subset simulation.  Opaque payloads, provider behavior, bytes,
persistence, cancellation delivery, and equivalence to the complete deployed TypeScript Harness
remain explicit nonclaims.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventSimulation

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionRefinement
open Cordis.DeepSeekHarnessEventIgnorableProjection
open Cordis.DeepSeekHarnessEventIgnorableNormalization

abbrev State := SessionRefinement.State

inductive SimulationError where
  | normalization (error : NormalizationError)
  | refinement (sourcePosition : Nat) (error : RefinementError)
deriving DecidableEq, Repr

/-- One retained source occurrence and the exact local transition it induces. -/
structure ReplayStep (before : State) (occurrence : NormalizedOccurrence) where
  refinement : RefinedEvent before occurrence.event

namespace ReplayStep

def after {before : State} {occurrence : NormalizedOccurrence}
    (step : ReplayStep before occurrence) : State :=
  step.refinement.after

theorem local_seq {before : State} {occurrence : NormalizedOccurrence}
    (_step : ReplayStep before occurrence) :
    occurrence.event.seq.value = occurrence.localPosition :=
  occurrence.seq_eq

end ReplayStep

/-! ## A dependent source/local trace -/

inductive SourceReplay : State → List NormalizedOccurrence → State → Type where
  | nil (state : State) : SourceReplay state [] state
  | cons {seed final : State} {occurrence : NormalizedOccurrence}
      {rest : List NormalizedOccurrence}
      (head : ReplayStep seed occurrence)
      (tail : SourceReplay head.after rest final) :
      SourceReplay seed (occurrence :: rest) final

namespace SourceReplay

def sourcePositions {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Nat :=
  fun _ => occurrences.map NormalizedOccurrence.sourcePosition

def sourceSequences {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Nat :=
  fun _ => occurrences.map (fun occurrence => occurrence.source.event.seq.value)

def sourceTimes {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Nat :=
  fun _ => occurrences.map (fun occurrence => occurrence.source.event.time.value)

def localSequences {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Nat :=
  fun _ => occurrences.map NormalizedOccurrence.localPosition

def sourceRaw {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Lean.Json :=
  fun _ => occurrences.map (fun occurrence => occurrence.source.raw)

def normalizedRaw {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → List Lean.Json :=
  fun _ => occurrences.map NormalizedOccurrence.raw

def toValidated {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → ValidatedSequence seed
      (occurrences.map NormalizedOccurrence.event) final
  | .nil state => .nil state
  | .cons head tail => .cons head.refinement tail.toValidated

def protocolTrace {seed final : State} {occurrences : List NormalizedOccurrence} :
    SourceReplay seed occurrences final → Cordis.Trace seed.protocol final.protocol :=
  fun replay => replay.toValidated.protocolTrace

theorem sourcePositions_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.sourcePositions = occurrences.map NormalizedOccurrence.sourcePosition := by
  rfl

theorem sourceSequences_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.sourceSequences = occurrences.map
      (fun occurrence => occurrence.source.event.seq.value) := by
  rfl

theorem sourceTimes_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.sourceTimes = occurrences.map
      (fun occurrence => occurrence.source.event.time.value) := by
  rfl

theorem localSequences_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.localSequences = occurrences.map NormalizedOccurrence.localPosition := by
  rfl

theorem sourceRaw_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.sourceRaw = occurrences.map (fun occurrence => occurrence.source.raw) := by
  rfl

theorem normalizedRaw_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.normalizedRaw = occurrences.map NormalizedOccurrence.raw := by
  rfl

theorem protocolTrace_erase {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    replay.protocolTrace.erase = replay.toValidated.runtimeEvents := by
  exact ValidatedSequence.protocolTrace_erase replay.toValidated

theorem sessionProjection_eq {seed final : State} {occurrences : List NormalizedOccurrence}
    (replay : SourceReplay seed occurrences final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection seed.session.events ++ replay.toValidated.runtimeEvents := by
  exact ValidatedSequence.sessionProjection_eq replay.toValidated

end SourceReplay

/-! ## Source ledger and executable replay -/

structure SourceLedger {input : List Lean.Json} (normalized : NormalizedLog input) where
  decisions : DecisionLedger normalized.projection.projection.decisions
    normalized.projection.occurrences
  kept_positions_eq :
    decisions.keptPositions = normalized.occurrences.map NormalizedOccurrence.sourcePosition

def sourceLedger {input : List Lean.Json} (normalized : NormalizedLog input) :
    SourceLedger normalized := by
  let decisions := SupportedProjection.decision_ledger normalized.projection
  exact {
    decisions
    kept_positions_eq := by
      rw [DecisionLedger.keptPositions_eq_sourcePositions decisions]
      exact normalized.occurrences_positions_eq.symm
  }

def replayOne (before : State) (occurrence : NormalizedOccurrence) :
    Except SimulationError (ReplayStep before occurrence) :=
  match refineEvent before occurrence.event with
  | .error error => .error (.refinement occurrence.sourcePosition error)
  | .ok refinement => .ok { refinement }

def replayOccurrences (seed : State) (occurrences : List NormalizedOccurrence) :
    Except SimulationError (Σ final, SourceReplay seed occurrences final) :=
  match occurrences with
  | [] => .ok ⟨seed, .nil seed⟩
  | occurrence :: rest =>
      match replayOne seed occurrence with
      | .error error => .error error
      | .ok head =>
          match replayOccurrences head.after rest with
          | .error error => .error error
          | .ok ⟨final, tail⟩ => .ok ⟨final, .cons head tail⟩

private theorem decodeOccurrencesAt :
    ∀ (index : Nat) (occurrences : List NormalizedOccurrence),
      occurrences.map NormalizedOccurrence.localPosition =
          (List.range occurrences.length).map (· + index) →
      SessionRefinement.decodeEventsAt index
          (occurrences.map NormalizedOccurrence.raw) =
        .ok (occurrences.map NormalizedOccurrence.event)
  | index, [], positions => by
      rfl
  | index, head :: tail, positions => by
      have headPosition : head.localPosition = index := by
        simp only [List.length_cons, List.range_succ_eq_map, List.map_cons] at positions
        simpa using congrArg List.head? positions
      have tailPositions :
          tail.map NormalizedOccurrence.localPosition =
            (List.range tail.length).map (· + (index + 1)) := by
        simp only [List.length_cons, List.range_succ_eq_map, List.map_cons] at positions
        have tailEq := congrArg List.tail? positions
        simpa [Function.comp_def, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using tailEq
      cases hTail : SessionRefinement.decodeEventsAt (index + 1)
          (tail.map NormalizedOccurrence.raw) with
      | error error =>
          change (do
            let event ← SessionRefinement.decodeEventAt [.index index] head.raw
            let events ← SessionRefinement.decodeEventsAt (index + 1)
              (tail.map NormalizedOccurrence.raw)
            .ok (event :: events)) =
            .ok (head.event :: tail.map NormalizedOccurrence.event)
          have headDecoded : SessionRefinement.decodeEventAt [.index index] head.raw =
              .ok head.event := by
            simpa [headPosition] using head.decoded
          have tailDecoded := decodeOccurrencesAt (index + 1) tail tailPositions
          rw [tailDecoded] at hTail
          cases hTail
      | ok events =>
          change (do
            let event ← SessionRefinement.decodeEventAt [.index index] head.raw
            let events ← SessionRefinement.decodeEventsAt (index + 1)
              (tail.map NormalizedOccurrence.raw)
            .ok (event :: events)) =
            .ok (head.event :: tail.map NormalizedOccurrence.event)
          have headDecoded : SessionRefinement.decodeEventAt [.index index] head.raw =
              .ok head.event := by
            simpa [headPosition] using head.decoded
          simp [headDecoded, hTail]
          have tailDecoded := decodeOccurrencesAt (index + 1) tail tailPositions
          rw [tailDecoded] at hTail
          cases hTail
          rfl

private theorem decodeOccurrences {occurrences : List NormalizedOccurrence}
    (positions : occurrences.map NormalizedOccurrence.localPosition =
      List.range occurrences.length) :
    SessionRefinement.decodeEvents (occurrences.map NormalizedOccurrence.raw) =
      .ok (occurrences.map NormalizedOccurrence.event) := by
  unfold SessionRefinement.decodeEvents
  simpa using decodeOccurrencesAt 0 occurrences (by simpa using positions)

theorem validated_events_eq_occurrences {input : List Lean.Json}
    (normalized : NormalizedLog input) :
    normalized.validated.events = normalized.occurrences.map NormalizedOccurrence.event := by
  have decoded := decodeOccurrences (occurrences := normalized.occurrences)
    normalized.occurrences_localPositions_eq
  have inputDecoded : SessionRefinement.decodeEvents normalized.normalizedInput =
      .ok (normalized.occurrences.map NormalizedOccurrence.event) := by
    rw [normalized.normalizedInput_eq]
    exact decoded
  have both : (.ok normalized.validated.events :
      Except SessionRefinement.DecodeError (List WireEvent)) =
      .ok (normalized.occurrences.map NormalizedOccurrence.event) :=
    normalized.validated.decode_eq.symm.trans inputDecoded
  exact Except.ok.inj both

private theorem replay_final_of_validate
    (seed : State)
    : ∀ (occurrences : List NormalizedOccurrence) (final : State)
      (sequence : ValidatedSequence seed
        (occurrences.map NormalizedOccurrence.event) final),
      SessionRefinement.validateSequence seed
          (occurrences.map NormalizedOccurrence.event) = .ok ⟨final, sequence⟩ →
        ∃ replay : SourceReplay seed occurrences final,
          replayOccurrences seed occurrences = .ok ⟨final, replay⟩
  | [], final, sequence, result => by
      cases sequence
      exact ⟨.nil seed, rfl⟩
  | occurrence :: rest, final, sequence, result => by
      cases headResult : SessionRefinement.refineEvent seed occurrence.event with
      | error error =>
          simp only [SessionRefinement.validateSequence, List.map] at result
          simp only [headResult, Except.bind, Bind.bind] at result
          cases result
      | ok head =>
          cases tailResult : SessionRefinement.validateSequence head.after
              (rest.map NormalizedOccurrence.event) with
          | error error =>
              simp only [SessionRefinement.validateSequence, List.map] at result
              simp only [headResult, tailResult, Except.bind, Bind.bind] at result
              cases result
          | ok tail =>
              cases sequence with
              | cons sequenceHead sequenceTail =>
                simp only [SessionRefinement.validateSequence, List.map] at result
                simp only [headResult, tailResult, Except.bind, Bind.bind] at result
                have resultEq := Except.ok.inj result
                cases resultEq
                have tailReplay := replay_final_of_validate head.after rest tail.1
                  tail.2 tailResult
                rcases tailReplay with ⟨replay, replayResult⟩
                refine ⟨.cons { refinement := head } replay, ?_⟩
                simp [ReplayStep.after, replayOccurrences, replayOne, headResult, replayResult]

private theorem replay_final_of_validate_events
    (seed : State)
    (occurrences : List NormalizedOccurrence) (events : List WireEvent) (final : State)
    (sequence : ValidatedSequence seed events final)
    (eventsEq : events = occurrences.map NormalizedOccurrence.event)
    (result : SessionRefinement.validateSequence seed events = .ok ⟨final, sequence⟩) :
    ∃ replay : SourceReplay seed occurrences final,
      replayOccurrences seed occurrences = .ok ⟨final, replay⟩ := by
  cases eventsEq
  exact replay_final_of_validate seed occurrences final sequence result

theorem replay_endpoint_eq_validated {input : List Lean.Json}
    (normalized : NormalizedLog input)
    {replay : Sigma (fun final => SourceReplay State.initial normalized.occurrences final)}
    (result : replayOccurrences State.initial normalized.occurrences = .ok replay) :
    replay.1 = normalized.validated.final := by
  have eventsEq := validated_events_eq_occurrences normalized
  rcases replay with ⟨final, replay⟩
  have aligned := replay_final_of_validate_events State.initial normalized.occurrences
    normalized.validated.events normalized.validated.final normalized.validated.sequence
    eventsEq normalized.validated.validate_eq
  rcases aligned with ⟨replay', replayResult'⟩
  have resultEq := Except.ok.inj (result.symm.trans replayResult')
  exact congrArg Sigma.fst resultEq

structure SimulationCertificate {input : List Lean.Json}
    (normalized : NormalizedLog input) where
  ledger : SourceLedger normalized
  replay : Σ final,
    SourceReplay State.initial normalized.occurrences final
  replay_endpoint_eq : replay.1 = normalized.validated.final

def simulateNormalized {input : List Lean.Json} (normalized : NormalizedLog input) :
    Except SimulationError (SimulationCertificate normalized) :=
  match replayResult : replayOccurrences State.initial normalized.occurrences with
  | .error error => .error error
  | .ok replay => .ok {
      ledger := sourceLedger normalized
      replay
      replay_endpoint_eq := replay_endpoint_eq_validated normalized replayResult
    }

/-! ## Deterministic executable evidence -/

def toolNormalizedSimulation :
    Except SimulationError
      (Σ normalized : NormalizedLog ignorableMiddleToolFixtureJson,
        SimulationCertificate normalized) :=
  match ignorableMiddleToolNormalized with
  | .error error => .error (.normalization error)
  | .ok normalized =>
      match simulateNormalized normalized with
      | .error error => .error error
      | .ok certificate => .ok ⟨normalized, certificate⟩

def toolSimulationSummary : Option (Nat × Nat × Nat × List Nat × List Nat) :=
  match toolNormalizedSimulation with
  | .error _ => none
  | .ok ⟨_, certificate⟩ =>
      some (
        certificate.ledger.decisions.keptPositions.length,
        certificate.ledger.decisions.droppedPositions.length,
        certificate.replay.1.session.nextSeq,
        certificate.replay.2.sourcePositions,
        certificate.replay.2.sourceTimes)

end Cordis.DeepSeekHarnessEventSimulation
