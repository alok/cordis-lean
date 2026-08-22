import Cordis.SessionEventArchive

/-!
# Explicitly ignorable current-Harness archive projection

The current Harness envelope permits an extension row to carry `ignorable: true`.  The archive
layer retains such a row losslessly, while the typed runner restore boundary quite correctly
refuses opaque input.  This module records the smallest honest bridge between those boundaries:
it projects a lossless archive into positional keep/drop decisions, drops only opaque rows that
are explicitly marked ignorable, and retains a typed certificate for every supported row.

The projection is not a `SessionRefinement.ValidatedJsonLog`.  Physical sequence numbers remain
the source numbers after a row is dropped, so a caller that wants local session replay must still
provide a sequence-renumbering and semantic-normalization certificate.  Required opaque rows
therefore fail the projection instead of being silently discarded.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventIgnorableProjection

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionRefinement

/-! ## Positional keep/drop ledger -/

def skippable (event : ArchivedEvent) : Bool :=
  event.isOpaque && !event.isRequired

theorem skippable_supported (certificate : Supported) :
    skippable (.supported certificate) = false := by
  rfl

inductive ProjectionDecision where
  | keep (position : Nat) (event : ArchivedEvent)
  | drop (position : Nat) (event : ArchivedEvent) (skippable : skippable event = true)

namespace ProjectionDecision

def event : ProjectionDecision → ArchivedEvent
  | .keep _ event | .drop _ event _ => event

def position : ProjectionDecision → Nat
  | .keep position _ | .drop position _ _ => position

def isDrop : ProjectionDecision → Bool
  | .keep _ _ => false
  | .drop _ _ _ => true

def isKeep : ProjectionDecision → Bool
  | .keep _ _ => true
  | .drop _ _ _ => false

end ProjectionDecision

private def makeDecisions : Nat → List ArchivedEvent → List ProjectionDecision
  | _, [] => []
  | position, event :: rest =>
      if skipped : skippable event then
        .drop position event skipped :: makeDecisions (position + 1) rest
      else
        .keep position event :: makeDecisions (position + 1) rest

theorem makeDecisions_length (position : Nat) (events : List ArchivedEvent) :
    (makeDecisions position events).length = events.length := by
  induction events generalizing position with
  | nil => rfl
  | cons head tail ih =>
      simp only [makeDecisions, List.length_cons]
      split <;> simp [ih]

theorem makeDecisions_events (position : Nat) (events : List ArchivedEvent) :
    (makeDecisions position events).map ProjectionDecision.event = events := by
  induction events generalizing position with
  | nil => rfl
  | cons head tail ih =>
      simp only [makeDecisions]
      split <;> simp [ProjectionDecision.event, ih]

structure Projection (input : List Lean.Json) where
  archive : ArchivedLog input
  decisions : List ProjectionDecision
  decisions_length : decisions.length = archive.events.length
  decisions_events : decisions.map ProjectionDecision.event = archive.events

def project {input : List Lean.Json} (archive : ArchivedLog input) : Projection input :=
  {
    archive
    decisions := makeDecisions 0 archive.events
    decisions_length := makeDecisions_length 0 archive.events
    decisions_events := makeDecisions_events 0 archive.events
  }

theorem Projection.source_raw {input : List Lean.Json} (projection : Projection input) :
    projection.decisions.map (fun decision => decision.event.raw) = input := by
  calc
    projection.decisions.map (fun decision => decision.event.raw) =
        (projection.decisions.map ProjectionDecision.event).map ArchivedEvent.raw := by
          simp [Function.comp_def]
    _ = projection.archive.events.map ArchivedEvent.raw := by
      rw [projection.decisions_events]
    _ = input := projection.archive.raw_exact

theorem Projection.source_length {input : List Lean.Json} (projection : Projection input) :
    projection.decisions.length = input.length := by
  rw [projection.decisions_length, projection.archive.length_exact]

/-! ## Supported occurrence output -/

inductive ProjectionError where
  | requiredOpaque (position : Nat) (eventType : String)
deriving Repr, DecidableEq

structure SupportedOccurrence where
  position : Nat
  certificate : Supported

namespace SupportedOccurrence

def raw (occurrence : SupportedOccurrence) : Lean.Json :=
  occurrence.certificate.known.raw

def event (occurrence : SupportedOccurrence) : WireEvent :=
  occurrence.certificate.event

theorem raw_eq (occurrence : SupportedOccurrence) :
    occurrence.raw = occurrence.certificate.known.envelope.raw :=
  rfl

theorem decoded_raw (occurrence : SupportedOccurrence) :
    SessionRefinement.decodeEvent occurrence.raw = .ok occurrence.event := by
  exact occurrence.certificate.decoded

end SupportedOccurrence

private def projectDecisions : List ProjectionDecision →
    Except ProjectionError (List SupportedOccurrence)
  | [] => .ok []
  | .drop _ _ _ :: rest => projectDecisions rest
  | .keep position (.supported certificate) :: rest => do
      let tail ← projectDecisions rest
      .ok ({ position, certificate } :: tail)
  | .keep position event :: _rest =>
      .error (.requiredOpaque position event.envelope.type)

structure SupportedProjection (input : List Lean.Json) where
  projection : Projection input
  occurrences : List SupportedOccurrence
  occurrences_eq :
    projectDecisions projection.decisions = .ok occurrences

def projectSupported {input : List Lean.Json} (archive : ArchivedLog input) :
    Except ProjectionError (SupportedProjection input) :=
  let projection := project archive
  match result : projectDecisions projection.decisions with
  | .error error => .error error
  | .ok occurrences =>
      .ok { projection, occurrences, occurrences_eq := result }

namespace SupportedProjection

def events {input : List Lean.Json} (projection : SupportedProjection input) : List WireEvent :=
  projection.occurrences.map SupportedOccurrence.event

def raws {input : List Lean.Json} (projection : SupportedProjection input) : List Lean.Json :=
  projection.occurrences.map SupportedOccurrence.raw

def positions {input : List Lean.Json} (projection : SupportedProjection input) : List Nat :=
  projection.occurrences.map SupportedOccurrence.position

theorem source_raw {input : List Lean.Json} (projection : SupportedProjection input) :
    projection.projection.decisions.map (fun decision => decision.event.raw) = input :=
  Projection.source_raw projection.projection

theorem occurrence_decode {input : List Lean.Json} (projection : SupportedProjection input) :
    ∀ occurrence ∈ projection.occurrences,
      SessionRefinement.decodeEvent occurrence.raw = .ok occurrence.event := by
  intro occurrence membership
  exact occurrence.decoded_raw

end SupportedProjection

/-! ## Executable archive fixtures -/

def ignorableTailJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/telemetry"), ("seq", .num 8), ("time", .num 308),
  ("data", Lean.Json.mkObj [("sample", .num 7)]), ("ignorable", .bool true)
]

def requiredTailJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/future-event"), ("seq", .num 8), ("time", .num 308),
  ("data", Lean.Json.mkObj [("opaque", .str "preserve-me")])
]

def ignorableFixtureJson : List Lean.Json :=
  SessionRefinement.toolMessageExampleJson ++ [ignorableTailJson]

def requiredFixtureJson : List Lean.Json :=
  SessionRefinement.toolMessageExampleJson ++ [requiredTailJson]

def ignorableFixtureProjection :
    Except ProjectionError (SupportedProjection ignorableFixtureJson) :=
  match _archiveResult : archive ignorableFixtureJson with
  | .error _ => .error (.requiredOpaque 0 "archive-error")
  | .ok archive => projectSupported archive

def requiredFixtureProjection :
    Except ProjectionError (SupportedProjection requiredFixtureJson) :=
  match _archiveResult : archive requiredFixtureJson with
  | .error _ => .error (.requiredOpaque 0 "archive-error")
  | .ok archive => projectSupported archive

def ignorableFixtureSummary : Option (Nat × Nat × List Nat) :=
  match ignorableFixtureProjection with
  | .error _ => none
  | .ok projection =>
      some (projection.projection.decisions.length, projection.occurrences.length,
        projection.positions)

def requiredFixtureSummary : Option ProjectionError :=
  match requiredFixtureProjection with
  | .error error => some error
  | .ok _ => none

theorem ignorable_fixture_summary :
    ignorableFixtureSummary = some (9, 8, [0, 1, 2, 3, 4, 5, 6, 7]) := by
  decide

theorem required_fixture_rejected :
    requiredFixtureSummary = some (.requiredOpaque 8 "vendor/future-event") := by
  decide

theorem ignorable_fixture_source_length :
    (match ignorableFixtureProjection with
    | .error _ => false
    | .ok projection => projection.projection.archive.events.length = 9) = true := by
  decide

end Cordis.DeepSeekHarnessEventIgnorableProjection
