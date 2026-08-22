import Cordis.DeepSeekHarnessEventSimulation

/-!
# Archive-aware replay for the supported current-Harness subset

`DeepSeekHarnessEventSimulation` certifies the normalized supported rows, while the archive
projection certifies that physical rows were either retained or explicitly dropped.  This module
combines those two facts in one dependent replay.  Its indexed `DecisionLedger.drop` constructor
consumes an ignorable opaque archive row without changing the state; a `keep` constructor
consumes a normalized occurrence together with the exact `RefinedEvent` transition it induces.
Required opaque rows
cannot enter the replay because the projection has no `drop` certificate for them.

The result is deliberately narrower than a deployed Harness equivalence: opaque payload
semantics, provider behavior, persistence, bytes, and cancellation remain outside this slice.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventArchiveReplay

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionRefinement
open Cordis.DeepSeekHarnessEventIgnorableProjection
open Cordis.DeepSeekHarnessEventIgnorableNormalization
open Cordis.DeepSeekHarnessEventSimulation

abbrev State := SessionRefinement.State

/-! ## Intrinsic archive/local alignment -/

structure ArchiveReplay (seed : State) (decisions : List ProjectionDecision)
    (occurrences : List NormalizedOccurrence) (final : State) where
  sourceReplay : SourceReplay seed occurrences final
  ledger : DecisionLedger decisions (occurrences.map NormalizedOccurrence.source)

def decisionDroppedRaw : List ProjectionDecision → List Lean.Json
  | [] => []
  | .drop _ event _ :: rest => event.raw :: decisionDroppedRaw rest
  | .keep _ _ :: rest => decisionDroppedRaw rest

def decisionDroppedPositions : List ProjectionDecision → List Nat
  | [] => []
  | .drop position _ _ :: rest => position :: decisionDroppedPositions rest
  | .keep _ _ :: rest => decisionDroppedPositions rest

namespace ArchiveReplay

def toSourceReplay {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    SourceReplay seed occurrences final :=
  replay.sourceReplay

def archiveRaw {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (_replay : ArchiveReplay seed decisions occurrences final) : List Lean.Json :=
  decisions.map (fun decision => decision.event.raw)

def keptRaw {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (_replay : ArchiveReplay seed decisions occurrences final) : List Lean.Json :=
  occurrences.map (fun occurrence => occurrence.source.raw)

def droppedRaw {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (_replay : ArchiveReplay seed decisions occurrences final) : List Lean.Json :=
  decisionDroppedRaw decisions

def droppedPositions {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (_replay : ArchiveReplay seed decisions occurrences final) : List Nat :=
  decisionDroppedPositions decisions

def keptPositions {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (_replay : ArchiveReplay seed decisions occurrences final) : List Nat :=
  occurrences.map NormalizedOccurrence.sourcePosition

theorem toSourceReplay_sourceRaw {seed final : State} {decisions : List ProjectionDecision}
    {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.toSourceReplay.sourceRaw = replay.keptRaw := by
  rfl

theorem toSourceReplay_normalizedRaw {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.toSourceReplay.normalizedRaw = occurrences.map NormalizedOccurrence.raw := by
  rfl

theorem archiveRaw_eq_decisions {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.archiveRaw = decisions.map (fun decision => decision.event.raw) := by
  rfl

theorem droppedRaw_eq_decisionDrops {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.droppedRaw = decisionDroppedRaw decisions := by
  rfl

theorem droppedPositions_eq_decisionDrops {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.droppedPositions = decisionDroppedPositions decisions := by
  rfl

theorem keptPositions_eq_sourcePositions {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.keptPositions = occurrences.map NormalizedOccurrence.sourcePosition := by
  rfl

theorem protocolTrace_erase {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    replay.toSourceReplay.protocolTrace.erase =
      replay.toSourceReplay.toValidated.runtimeEvents := by
  exact SourceReplay.protocolTrace_erase replay.toSourceReplay

theorem sessionProjection_eq {seed final : State}
    {decisions : List ProjectionDecision} {occurrences : List NormalizedOccurrence}
    (replay : ArchiveReplay seed decisions occurrences final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection seed.session.events ++
        replay.toSourceReplay.toValidated.runtimeEvents := by
  exact SourceReplay.sessionProjection_eq replay.toSourceReplay

end ArchiveReplay

/-! ## Construction from the already-certified normalized simulation -/

structure ArchiveReplayCertificate {input : List Lean.Json}
    (normalized : NormalizedLog input) where
  simulation : SimulationCertificate normalized
  archive : ArchiveReplay State.initial normalized.projection.projection.decisions
    normalized.occurrences simulation.replay.1
  normalized_replay : archive.toSourceReplay = simulation.replay.2
  archive_raw_eq : archive.archiveRaw = normalized.projection.projection.archive.events.map
    ArchivedEvent.raw
  source_raw_eq : archive.keptRaw = normalized.occurrences.map
    (fun occurrence => occurrence.source.raw)
  dropped_raw_eq : archive.droppedRaw = decisionDroppedRaw
    normalized.projection.projection.decisions

def archiveReplay {input : List Lean.Json} (normalized : NormalizedLog input)
    (simulation : SimulationCertificate normalized) :
    ArchiveReplayCertificate normalized := by
  have ledger : DecisionLedger normalized.projection.projection.decisions
      (normalized.occurrences.map NormalizedOccurrence.source) := by
    rw [normalized.occurrences_sources_eq]
    exact simulation.ledger.decisions
  exact {
    simulation
    archive := {
      sourceReplay := simulation.replay.2
      ledger
    }
    normalized_replay := by
      rfl
    archive_raw_eq := by
      rw [ArchiveReplay.archiveRaw_eq_decisions]
      calc
        normalized.projection.projection.decisions.map
            (fun decision => decision.event.raw) =
            (normalized.projection.projection.decisions.map ProjectionDecision.event).map
              ArchivedEvent.raw := by
                simp [Function.comp_def]
        _ = normalized.projection.projection.archive.events.map ArchivedEvent.raw := by
          rw [normalized.projection.projection.decisions_events]
    source_raw_eq := by
      rfl
    dropped_raw_eq := by
      exact ArchiveReplay.droppedRaw_eq_decisionDrops {
        sourceReplay := simulation.replay.2
        ledger
      }
  }

def toolArchiveReplay :
    Except SimulationError
      (Σ normalized : NormalizedLog ignorableMiddleToolFixtureJson,
        ArchiveReplayCertificate normalized) :=
  match toolNormalizedSimulation with
  | .error error => .error error
  | .ok ⟨normalized, simulation⟩ => .ok ⟨normalized, archiveReplay normalized simulation⟩

def toolArchiveReplaySummary : Option (Nat × Nat × Nat × List Nat) :=
  match toolArchiveReplay with
  | .error _ => none
  | .ok ⟨_, certificate⟩ =>
      some (certificate.archive.keptRaw.length,
        certificate.archive.droppedRaw.length,
        certificate.archive.archiveRaw.length,
        certificate.archive.droppedPositions)

theorem tool_archive_replay_source_raw {normalized : NormalizedLog ignorableMiddleToolFixtureJson}
    (certificate : ArchiveReplayCertificate normalized) :
    certificate.archive.toSourceReplay.sourceRaw = certificate.archive.keptRaw := by
  exact ArchiveReplay.toSourceReplay_sourceRaw certificate.archive

end Cordis.DeepSeekHarnessEventArchiveReplay
