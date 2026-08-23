import Cordis.DeepSeekHarnessEventSimulation

/-!
# Complete supported-subset current-Harness event simulations

This module composes the source-shaped current-Harness archive, ignorable-row normalization,
and occurrence-indexed semantic replay into one dependent JSON-log result. A successful
`CompleteSimulation` retains every input AST in order, the normalized keep/drop ledger, and a
`SourceReplay` whose every retained event is indexed by its exact pre-state. The replay therefore
proves protocol erasure and the final session projection equation rather than merely reporting a
decoded list.

The three fixtures cover the supported user/assistant surface, assistant tool-call plus tool-result
surface, and a compaction-style replacement. A malformed replacement is checked to fail closed.
This is still a source-honest finite subset: opaque/extension semantics, provider behavior,
transport, bytes, persistence, cancellation delivery, and equivalence to the complete deployed
TypeScript Harness remain outside the claim.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessCompleteSimulation

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionRefinement
open Cordis.DeepSeekHarnessEventIgnorableNormalization
open Cordis.DeepSeekHarnessEventSimulation

inductive SimulationError where
  | archive (error : ArchiveError)
  | normalization (error : NormalizationError)
  | replay (error : DeepSeekHarnessEventSimulation.SimulationError)
deriving BEq, DecidableEq, Repr

structure CompleteSimulation (input : List Lean.Json) where
  archive : ArchivedLog input
  normalized : NormalizedLog input
  certificate : SimulationCertificate normalized

def simulate (input : List Lean.Json) : Except SimulationError (CompleteSimulation input) :=
  match archive input with
  | .error error => .error (.archive error)
  | .ok archived =>
      match normalize archived with
      | .error error => .error (.normalization error)
      | .ok normalized =>
          match simulateNormalized normalized with
          | .error error => .error (.replay error)
          | .ok certificate => .ok { archive := archived, normalized, certificate }

structure Summary where
  archivedLength : Nat
  knownCount : Nat
  keptCount : Nat
  droppedCount : Nat
  finalNextSeq : Nat
  finalMessageCount : Nat
  sourcePositions : List Nat
  sourceTimes : List Nat
deriving BEq, DecidableEq, Repr

def CompleteSimulation.summary {input : List Lean.Json}
    (simulation : CompleteSimulation input) : Summary :=
  let replay := simulation.certificate.replay
  {
    archivedLength := simulation.archive.events.length
    knownCount := simulation.archive.knownCount
    keptCount := simulation.certificate.ledger.decisions.keptPositions.length
    droppedCount := simulation.certificate.ledger.decisions.droppedPositions.length
    finalNextSeq := replay.1.session.nextSeq
    finalMessageCount := replay.1.session.messages.length
    sourcePositions := replay.2.sourcePositions
    sourceTimes := replay.2.sourceTimes
  }

def summarize (input : List Lean.Json) : Except SimulationError Summary :=
  (CompleteSimulation.summary <$> simulate input)

theorem archive_raw_exact {input : List Lean.Json}
    (simulation : CompleteSimulation input) :
    simulation.archive.events.map ArchivedEvent.raw = input :=
  simulation.archive.raw_exact

theorem protocolTrace_erase {input : List Lean.Json}
    (simulation : CompleteSimulation input) :
    simulation.certificate.replay.2.protocolTrace.erase =
      simulation.certificate.replay.2.toValidated.runtimeEvents :=
  simulation.certificate.replay.2.protocolTrace_erase

theorem sessionProjection_eq {input : List Lean.Json}
    (simulation : CompleteSimulation input) :
    Session.protocolProjection simulation.certificate.replay.1.session.events =
      Session.protocolProjection State.initial.session.events ++
        simulation.certificate.replay.2.toValidated.runtimeEvents :=
  simulation.certificate.replay.2.sessionProjection_eq

def textSummary : Except SimulationError Summary :=
  summarize SessionRefinement.messageExampleJson

def toolSummary : Except SimulationError Summary :=
  summarize SessionRefinement.toolMessageExampleJson

def replacementSummary : Except SimulationError Summary :=
  summarize SessionRefinement.replacementMessageExampleJson

def malformedReplacementRejected : Bool :=
  match summarize SessionRefinement.malformedReplacementMessageExampleJson with
  | .error _ => true
  | .ok _ => false

def executableTextSummary : Summary := {
  archivedLength := 6
  knownCount := 6
  keptCount := 6
  droppedCount := 0
  finalNextSeq := 6
  finalMessageCount := 2
  sourcePositions := [0, 1, 2, 3, 4, 5]
  sourceTimes := [200, 201, 202, 203, 204, 205]
}

def executableToolSummary : Summary := {
  archivedLength := 8
  knownCount := 8
  keptCount := 8
  droppedCount := 0
  finalNextSeq := 8
  finalMessageCount := 3
  sourcePositions := [0, 1, 2, 3, 4, 5, 6, 7]
  sourceTimes := [300, 301, 302, 303, 304, 305, 306, 307]
}

def executableReplacementSummary : Summary := {
  archivedLength := 9
  knownCount := 9
  keptCount := 9
  droppedCount := 0
  finalNextSeq := 9
  finalMessageCount := 2
  sourcePositions := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  sourceTimes := [300, 301, 302, 303, 304, 305, 306, 307, 308]
}

end Cordis.DeepSeekHarnessCompleteSimulation
