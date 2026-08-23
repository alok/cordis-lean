import Cordis.DeepSeekHarnessCompleteSimulation
import Cordis.SessionPayloadArchive

/-!
# Payload-aware complete current-Harness simulations

`DeepSeekHarnessCompleteSimulation` composes the lossless event archive, supported-subset
normalization, and occurrence-indexed semantic replay.  This module adds the adjacent payload
ledger without changing that semantic boundary: every successful simulation gets a
`SessionPayloadArchive.PayloadLog` over the same archived input, so reasoning/image blocks,
assistant usage, tool-result error/meta objects, and unknown extension block tags remain available
beside the validated local session.

The payload pass is intentionally classification and retention, not an invented provider schema.
Known malformed payloads become typed opaque archive entries, and extension rows remain opaque.
The successful fixtures are therefore evidence for a finite source-shaped subset, not a theorem of
opaque semantics, provider behavior, transport, persistence, cancellation delivery, or deployed
TypeScript-Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadSimulation

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionPayloadArchive
open Cordis.SessionRefinement
open Cordis.DeepSeekHarnessCompleteSimulation

structure PayloadSimulation (input : List Lean.Json) where
  complete : CompleteSimulation input
  payload : PayloadLog input
  payload_source : payload.source = complete.archive

def simulate (input : List Lean.Json) :
    Except SimulationError (PayloadSimulation input) :=
  match DeepSeekHarnessCompleteSimulation.simulate input with
  | .error error => .error error
  | .ok complete =>
      let payload := SessionPayloadArchive.enrich complete.archive
      .ok { complete, payload, payload_source := rfl }

def payloadUsageCount : List EnrichedEvent → Nat
  | [] => 0
  | .typed _ payload :: rest =>
      (if payload.usage.isSome then 1 else 0) + payloadUsageCount rest
  | _ :: rest => payloadUsageCount rest

def payloadErrorMetaCount : List EnrichedEvent → Nat
  | [] => 0
  | .typed _ payload :: rest =>
      (if payload.errorJson.isSome && payload.metaJson.isSome then 1 else 0) +
        payloadErrorMetaCount rest
  | _ :: rest => payloadErrorMetaCount rest

structure Summary where
  archivedLength : Nat
  knownCount : Nat
  typedCount : Nat
  payloadTags : List (Option SessionPayloadArchive.KnownTag)
  blockTags : List (Option (List BlockTag))
  usageCount : Nat
  errorMetaCount : Nat
  finalNextSeq : Nat
  finalMessageCount : Nat
  sourcePositions : List Nat
  sourceTimes : List Nat
deriving BEq, DecidableEq, Repr

def PayloadSimulation.summary {input : List Lean.Json}
    (simulation : PayloadSimulation input) : Summary :=
  let complete := simulation.complete.summary
  {
    archivedLength := complete.archivedLength
    knownCount := complete.knownCount
    typedCount := simulation.payload.typedCount
    payloadTags := simulation.payload.events.map EnrichedEvent.tag?
    blockTags := simulation.payload.events.map EnrichedEvent.blockTags
    usageCount := payloadUsageCount simulation.payload.events
    errorMetaCount := payloadErrorMetaCount simulation.payload.events
    finalNextSeq := complete.finalNextSeq
    finalMessageCount := complete.finalMessageCount
    sourcePositions := complete.sourcePositions
    sourceTimes := complete.sourceTimes
  }

def summarize (input : List Lean.Json) : Except SimulationError Summary :=
  (PayloadSimulation.summary <$> simulate input)

theorem complete_archive_raw_exact {input : List Lean.Json}
    (simulation : PayloadSimulation input) :
    simulation.complete.archive.events.map ArchivedEvent.raw = input :=
  DeepSeekHarnessCompleteSimulation.archive_raw_exact simulation.complete

theorem payload_raw_exact {input : List Lean.Json}
    (simulation : PayloadSimulation input) :
    simulation.payload.events.map EnrichedEvent.raw = input := by
  exact simulation.payload.raw_exact

theorem payload_length_exact {input : List Lean.Json}
    (simulation : PayloadSimulation input) :
    simulation.payload.events.length = input.length :=
  simulation.payload.length_exact

theorem protocolTrace_erase {input : List Lean.Json}
    (simulation : PayloadSimulation input) :
    simulation.complete.certificate.replay.2.protocolTrace.erase =
      simulation.complete.certificate.replay.2.toValidated.runtimeEvents :=
  DeepSeekHarnessCompleteSimulation.protocolTrace_erase simulation.complete

theorem sessionProjection_eq {input : List Lean.Json}
    (simulation : PayloadSimulation input) :
    Session.protocolProjection simulation.complete.certificate.replay.1.session.events =
      Session.protocolProjection State.initial.session.events ++
        simulation.complete.certificate.replay.2.toValidated.runtimeEvents :=
  DeepSeekHarnessCompleteSimulation.sessionProjection_eq simulation.complete

def textSummary : Except SimulationError Summary :=
  summarize SessionRefinement.messageExampleJson

def toolSummary : Except SimulationError Summary :=
  summarize SessionRefinement.toolMessageExampleJson

def replacementSummary : Except SimulationError Summary :=
  summarize SessionRefinement.replacementMessageExampleJson

def executableTextSummary : Summary := {
  archivedLength := 6
  knownCount := 6
  typedCount := 6
  payloadTags := [some .turnStart, some .userMessage, some .stepStart,
    some .assistantMessage, some .stepEnd, some .turnEnd]
  blockTags := [none, some [.text], none, some [.reasoning, .image, .text], none, none]
  usageCount := 1
  errorMetaCount := 0
  finalNextSeq := 6
  finalMessageCount := 2
  sourcePositions := [0, 1, 2, 3, 4, 5]
  sourceTimes := [200, 201, 202, 203, 204, 205]
}

def executableToolSummary : Summary := {
  archivedLength := 8
  knownCount := 8
  typedCount := 8
  payloadTags := [some .turnStart, some .userMessage, some .stepStart,
    some .assistantMessage, some .toolCall, some .toolResult, some .stepEnd,
    some .turnEnd]
  blockTags := [none, some [.text], none, some [.text, .toolCall], none,
    some [.toolResult], none, none]
  usageCount := 0
  errorMetaCount := 0
  finalNextSeq := 8
  finalMessageCount := 3
  sourcePositions := [0, 1, 2, 3, 4, 5, 6, 7]
  sourceTimes := [300, 301, 302, 303, 304, 305, 306, 307]
}

def executableReplacementSummary : Summary := {
  archivedLength := 9
  knownCount := 9
  typedCount := 9
  payloadTags := [some .turnStart, some .userMessage, some .stepStart,
    some .assistantMessage, some .toolCall, some .toolResult, some .stepEnd,
    some .turnEnd, some .assistantMessage]
  blockTags := [none, some [.text], none, some [.text, .toolCall], none,
    some [.toolResult], none, none, some [.text]]
  usageCount := 0
  errorMetaCount := 0
  finalNextSeq := 9
  finalMessageCount := 2
  sourcePositions := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  sourceTimes := [300, 301, 302, 303, 304, 305, 306, 307, 308]
}

def reasoningImageArchiveRetained : Bool :=
  SessionPayloadArchive.reasoningImageTyped &&
    SessionPayloadArchive.assistantUsageCaptured

def toolResultErrorMetaRetained : Bool :=
  SessionPayloadArchive.toolResultOpaqueTyped &&
    SessionPayloadArchive.toolResultErrorMetaCaptured

def unknownBlockRetained : Bool :=
  SessionPayloadArchive.unknownBlockRetained

def malformedPayloadRetained : Bool :=
  SessionPayloadArchive.malformedPayloadIsRetained

end Cordis.DeepSeekHarnessPayloadSimulation
