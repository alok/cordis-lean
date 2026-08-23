import Cordis.DeepSeekHarnessEventIgnorableProjection

/-!
# Sequence normalization after explicitly ignorable rows

`DeepSeekHarnessEventIgnorableProjection` deliberately preserves physical archive sequence numbers.
This module supplies the next, still bounded, certificate: after an archive has been projected,
every retained supported event is rewritten to its contiguous local sequence, and every supported
`sourceEventSeqs`/`surfaceOp` reference is rewritten through the same physical-to-local map.

The result is then passed to `SessionRefinement.validateJsonLog`, so local replay is not a raw list
filter.  Duplicate physical sequence numbers, missing references, malformed rewrites, required
opaque rows, and semantic validation failures all reject.  This is a source-honest supported-event
normalization slice; it does not claim complete opaque-payload semantics or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventIgnorableNormalization

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionRefinement
open Cordis.DeepSeekHarnessEventIgnorableProjection

def jsonNat (value : Nat) : Lean.Json := .num (Lean.JsonNumber.fromNat value)

def setField (name : String) (value : Lean.Json) : Lean.Json → Lean.Json
  | .obj fields => .obj (fields.insert name value)
  | json => json

def setSeq (value : Nat) (json : Lean.Json) : Lean.Json := setField "seq" (jsonNat value) json

def seqMap : List ProjectionDecision → Nat → Option Nat
  | [], _ => none
  | .drop _ _ _ :: rest, physical => seqMap rest physical
  | .keep _ event :: rest, physical =>
      if event.envelope.seq.value = physical then
        some 0
      else
        (seqMap rest physical).map (· + 1)

def mapPhysical (decisions : List ProjectionDecision) (position physical : Nat) :
    Except String Nat :=
  match seqMap decisions physical with
  | some value => .ok value
  | none => .error ("missing source " ++ toString physical ++ " at " ++ toString position)

def mapSeqList (decisions : List ProjectionDecision) (position : Nat) :
    List Nat → Except String (List Nat)
  | [] => .ok []
  | head :: tail => do
      let mapped ← mapPhysical decisions position head
      let rest ← mapSeqList decisions position tail
      .ok (mapped :: rest)

def jsonNatList (values : List Nat) : Lean.Json :=
  .arr (values.toArray.map jsonNat)

def setOptionalSeqs (value : Option (List Nat)) (json : Lean.Json) : Lean.Json :=
  match value with
  | none => json
  | some values => setField "sourceEventSeqs" (jsonNatList values) json

def jsonMappedSurfaceOp (decisions : List ProjectionDecision) (position : Nat) :
    WireSurfaceOp → Except String Lean.Json
  | .append => .ok (.str "append")
  | .replace start endSeq => do
      let mappedStart ← mapPhysical decisions position start.value
      let mappedEnd ← mapPhysical decisions position endSeq.value
      .ok (Lean.Json.mkObj [
        ("op", .str "replace"), ("start", jsonNat mappedStart),
        ("end", jsonNat mappedEnd)])

def normalizedRaw (decisions : List ProjectionDecision) (position localSeq : Nat)
    (occurrence : SupportedOccurrence) : Except String Lean.Json := do
  let base := setSeq localSeq occurrence.raw
  match occurrence.event.payload with
  | .userMessage append => do
      let sources ← match append.sourceEventSeqs with
        | none => .ok none
        | some values => some <$> mapSeqList decisions position (values.map (·.value))
      let op ← jsonMappedSurfaceOp decisions position append.surfaceOp
      .ok (setField "surfaceOp" op (setOptionalSeqs sources base))
  | .assistantMessage _ _ append => do
      let sources ← match append.sourceEventSeqs with
        | none => .ok none
        | some values => some <$> mapSeqList decisions position (values.map (·.value))
      let op ← jsonMappedSurfaceOp decisions position append.surfaceOp
      .ok (setField "surfaceOp" op (setOptionalSeqs sources base))
  | .toolResult result => do
      let sources ← mapSeqList decisions position (result.sourceEventSeqs.map (·.value))
      let op ← jsonMappedSurfaceOp decisions position result.surfaceOp
      .ok (setField "surfaceOp" op
        (setField "sourceEventSeqs" (jsonNatList sources) base))
  | _ => .ok base

inductive NormalizationError where
  | archive (error : SessionEventArchive.ArchiveError)
  | projection (error : ProjectionError)
  | duplicatePhysicalSequences
  | missingReference (position physical : Nat)
  | rawRewrite (position : Nat) (message : String)
  | decode (position : Nat) (error : SessionRefinement.DecodeError)
  | decodeLog (error : SessionRefinement.DecodeError)
  | validation (error : SessionRefinement.RefinementError)
deriving DecidableEq, Repr

structure NormalizedOccurrence where
  sourcePosition : Nat
  localPosition : Nat
  source : SupportedOccurrence
  raw : Lean.Json
  event : WireEvent
  /-- The occurrence is decoded at the exact list path used by `decodeEvents`. -/
  decoded : SessionRefinement.decodeEventAt [.index localPosition] raw = .ok event
  seq_eq : event.seq.value = localPosition

private def normalizeOne (decisions : List ProjectionDecision) (localSeq : Nat)
    (occurrence : SupportedOccurrence) : Except NormalizationError NormalizedOccurrence :=
  match _rawResult : normalizedRaw decisions occurrence.position localSeq occurrence with
  | .error error => .error (.rawRewrite occurrence.position error)
  | .ok raw =>
      match decoded : SessionRefinement.decodeEventAt [.index localSeq] raw with
      | .error error => .error (.decode occurrence.position error)
      | .ok event =>
          if sequence : event.seq.value = localSeq then
            .ok {
              sourcePosition := occurrence.position
              localPosition := localSeq
              source := occurrence
              raw
              event
              decoded
              seq_eq := sequence
            }
          else
            .error (.rawRewrite occurrence.position "rewritten sequence did not normalize")

private def normalizeOccurrences (decisions : List ProjectionDecision) (localSeq : Nat) :
    List SupportedOccurrence → Except NormalizationError (List NormalizedOccurrence)
  | [] => .ok []
  | head :: tail => do
      let normalized ← normalizeOne decisions localSeq head
      let rest ← normalizeOccurrences decisions (localSeq + 1) tail
      .ok (normalized :: rest)

private theorem normalizeOne_source
    (decisions : List ProjectionDecision) (localSeq : Nat)
    (occurrence : SupportedOccurrence) (normalized : NormalizedOccurrence)
    (result : normalizeOne decisions localSeq occurrence = .ok normalized) :
    normalized.source = occurrence := by
  unfold normalizeOne at result
  split at result
  · contradiction
  · rename_i raw rawResult
    split at result
    · contradiction
    · rename_i event decoded
      split at result
      · cases result
        rfl
      · contradiction

private theorem normalizeOne_position
    (decisions : List ProjectionDecision) (localSeq : Nat)
    (occurrence : SupportedOccurrence) (normalized : NormalizedOccurrence)
    (result : normalizeOne decisions localSeq occurrence = .ok normalized) :
    normalized.sourcePosition = occurrence.position := by
  unfold normalizeOne at result
  split at result
  · contradiction
  · rename_i raw rawResult
    split at result
    · contradiction
    · rename_i event decoded
      split at result
      · cases result
        rfl
      · contradiction

private theorem normalizeOne_localPosition
    (decisions : List ProjectionDecision) (localSeq : Nat)
    (occurrence : SupportedOccurrence) (normalized : NormalizedOccurrence)
    (result : normalizeOne decisions localSeq occurrence = .ok normalized) :
    normalized.localPosition = localSeq := by
  unfold normalizeOne at result
  split at result
  · contradiction
  · rename_i raw rawResult
    split at result
    · contradiction
    · rename_i event decoded
      split at result
      · cases result
        rfl
      · contradiction

private theorem normalizeOccurrences_sources :
    ∀ (decisions : List ProjectionDecision) (localSeq : Nat)
      (occurrences : List SupportedOccurrence) (normalized : List NormalizedOccurrence),
      normalizeOccurrences decisions localSeq occurrences = .ok normalized →
        normalized.map NormalizedOccurrence.source = occurrences
  | _, _, [], normalized, result => by
      unfold normalizeOccurrences at result
      have normalized_eq : normalized = [] := (Except.ok.inj result).symm
      subst normalized
      rfl
  | decisions, localSeq, head :: tail, normalized, result => by
      cases hHead : normalizeOne decisions localSeq head with
      | error error =>
          unfold normalizeOccurrences at result
          rw [hHead] at result
          cases result
      | ok normalizedHead =>
          cases hTail : normalizeOccurrences decisions (localSeq + 1) tail with
          | error error =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              cases result
          | ok normalizedTail =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              have normalized_eq : normalized = normalizedHead :: normalizedTail :=
                (Except.ok.inj result).symm
              subst normalized
              simp [normalizeOne_source decisions localSeq head normalizedHead hHead,
                normalizeOccurrences_sources decisions (localSeq + 1) tail normalizedTail hTail]

private theorem normalizeOccurrences_positions :
    ∀ (decisions : List ProjectionDecision) (localSeq : Nat)
      (occurrences : List SupportedOccurrence) (normalized : List NormalizedOccurrence),
      normalizeOccurrences decisions localSeq occurrences = .ok normalized →
        normalized.map NormalizedOccurrence.sourcePosition =
          occurrences.map SupportedOccurrence.position
  | _, _, [], normalized, result => by
      unfold normalizeOccurrences at result
      have normalized_eq : normalized = [] := (Except.ok.inj result).symm
      subst normalized
      rfl
  | decisions, localSeq, head :: tail, normalized, result => by
      cases hHead : normalizeOne decisions localSeq head with
      | error error =>
          unfold normalizeOccurrences at result
          rw [hHead] at result
          cases result
      | ok normalizedHead =>
          cases hTail : normalizeOccurrences decisions (localSeq + 1) tail with
          | error error =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              cases result
          | ok normalizedTail =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              have normalized_eq : normalized = normalizedHead :: normalizedTail :=
                (Except.ok.inj result).symm
              subst normalized
              simp [normalizeOne_position decisions localSeq head normalizedHead hHead,
                normalizeOccurrences_positions decisions (localSeq + 1) tail normalizedTail hTail]

private theorem range_shift_positions (length offset : Nat) :
    offset :: (List.range length).map (· + (offset + 1)) =
      (List.range (length + 1)).map (· + offset) := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [← List.cons_append, inductionHypothesis]
      rw [List.range_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

private theorem normalizeOccurrences_localPositions :
    ∀ (decisions : List ProjectionDecision) (localSeq : Nat)
      (occurrences : List SupportedOccurrence) (normalized : List NormalizedOccurrence),
      normalizeOccurrences decisions localSeq occurrences = .ok normalized →
        normalized.map NormalizedOccurrence.localPosition =
          (List.range normalized.length).map (· + localSeq)
  | _, localSeq, [], normalized, result => by
      unfold normalizeOccurrences at result
      have normalized_eq : normalized = [] := (Except.ok.inj result).symm
      subst normalized
      rfl
  | decisions, localSeq, head :: tail, normalized, result => by
      cases hHead : normalizeOne decisions localSeq head with
      | error error =>
          unfold normalizeOccurrences at result
          rw [hHead] at result
          cases result
      | ok normalizedHead =>
          cases hTail : normalizeOccurrences decisions (localSeq + 1) tail with
          | error error =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              cases result
          | ok normalizedTail =>
              unfold normalizeOccurrences at result
              rw [hHead, hTail] at result
              have normalized_eq : normalized = normalizedHead :: normalizedTail :=
                (Except.ok.inj result).symm
              subst normalized
              have headPosition := normalizeOne_localPosition decisions localSeq head
                normalizedHead hHead
              have tailPositions := normalizeOccurrences_localPositions decisions (localSeq + 1)
                tail normalizedTail hTail
              simp only [List.length_cons, List.map_cons, headPosition]
              rw [tailPositions]
              exact range_shift_positions normalizedTail.length localSeq

def physicalSequences (decisions : List ProjectionDecision) : List Nat :=
  decisions.map (fun decision => decision.event.envelope.seq.value)

structure NormalizedLog (input : List Lean.Json) where
  projection : SupportedProjection input
  occurrences : List NormalizedOccurrence
  occurrences_sources_eq :
    occurrences.map NormalizedOccurrence.source = projection.occurrences
  occurrences_positions_eq :
    occurrences.map NormalizedOccurrence.sourcePosition =
      projection.occurrences.map SupportedOccurrence.position
  occurrences_localPositions_eq :
    occurrences.map NormalizedOccurrence.localPosition = List.range occurrences.length
  normalizedInput : List Lean.Json
  normalizedInput_eq : normalizedInput = occurrences.map NormalizedOccurrence.raw
  validated : SessionRefinement.ValidatedJsonLog normalizedInput
  validated_eq : SessionRefinement.validateJsonLog normalizedInput = .ok validated

def normalize {input : List Lean.Json} (archive : ArchivedLog input) :
    Except NormalizationError (NormalizedLog input) :=
  match _projectionResult : projectSupported archive with
  | .error error => .error (.projection error)
  | .ok projection =>
      if _nodup : (physicalSequences projection.projection.decisions).Nodup then
        match occurrencesResult : normalizeOccurrences projection.projection.decisions 0
          projection.occurrences with
        | .error error => .error error
        | .ok occurrences =>
            let normalizedInput := occurrences.map NormalizedOccurrence.raw
            match validatedResult : SessionRefinement.validateJsonLog normalizedInput with
            | .error (.inl error) => .error (.decodeLog error)
            | .error (.inr error) => .error (.validation error)
            | .ok validated =>
                .ok {
                  projection
                  occurrences
                  occurrences_sources_eq :=
                    normalizeOccurrences_sources projection.projection.decisions 0
                      projection.occurrences occurrences occurrencesResult
                  occurrences_positions_eq :=
                    normalizeOccurrences_positions projection.projection.decisions 0
                      projection.occurrences occurrences occurrencesResult
                  occurrences_localPositions_eq := by
                    have positions := normalizeOccurrences_localPositions
                      projection.projection.decisions 0 projection.occurrences occurrences
                      occurrencesResult
                    simpa using positions
                  normalizedInput
                  normalizedInput_eq := rfl
                  validated
                  validated_eq := validatedResult
                }
      else
        .error .duplicatePhysicalSequences

/-! ## An executable middle-row fixture -/

def shiftTailSeq : Nat → List Lean.Json → List Lean.Json
  | _, [] => []
  | next, head :: tail => setSeq next head :: shiftTailSeq (next + 1) tail

def ignorableMiddleJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/telemetry"), ("seq", .num 1), ("time", .num 450),
  ("data", Lean.Json.mkObj [("sample", .num 7)]), ("ignorable", .bool true)]

def ignorableMiddleToolJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/telemetry"), ("seq", .num 2), ("time", .num 450),
  ("data", Lean.Json.mkObj [("sample", .num 7)]), ("ignorable", .bool true)]

def ignorableMiddleFixtureJson : List Lean.Json :=
  match SessionRefinement.headerChunkExampleJson with
  | first :: tail => first :: ignorableMiddleJson :: shiftTailSeq 2 tail
  | [] => []

def ignorableMiddleArchive :
    Except SessionEventArchive.ArchiveError
      (ArchivedLog ignorableMiddleFixtureJson) :=
  archive ignorableMiddleFixtureJson

def ignorableMiddleNormalized :
    Except NormalizationError (NormalizedLog ignorableMiddleFixtureJson) :=
  match ignorableMiddleArchive with
  | .error error => .error (.archive error)
  | .ok archive => normalize archive

def ignorableMiddleSummary : Option (Nat × Nat × Nat × Nat) :=
  match ignorableMiddleNormalized with
  | .error _ => none
  | .ok normalized =>
      some (normalized.projection.projection.decisions.length,
        normalized.occurrences.length,
        normalized.validated.final.session.nextSeq,
        normalized.occurrences.head?.map (·.event.seq.value) |>.getD 99)

theorem ignorable_middle_summary :
    ignorableMiddleSummary = some (7, 6, 6, 0) := by
  rfl

theorem ignorable_middle_source_positions :
    match ignorableMiddleNormalized with
    | .error _ => false
    | .ok normalized => normalized.occurrences.map NormalizedOccurrence.sourcePosition =
        [0, 2, 3, 4, 5, 6] := by
  rfl

def ignorableMiddleToolFixtureJson : List Lean.Json :=
  match SessionRefinement.toolMessageExampleJson with
  | first :: second :: tail =>
      first :: second :: ignorableMiddleToolJson :: shiftTailSeq 3 tail
  | _ => []

def ignorableMiddleToolArchive :
    Except SessionEventArchive.ArchiveError
      (ArchivedLog ignorableMiddleToolFixtureJson) :=
  archive ignorableMiddleToolFixtureJson

def ignorableMiddleToolNormalized :
    Except NormalizationError (NormalizedLog ignorableMiddleToolFixtureJson) :=
  match ignorableMiddleToolArchive with
  | .error error => .error (.archive error)
  | .ok archive => normalize archive

def ignorableMiddleToolSummary : Option (Nat × Nat × Nat × Nat) :=
  match ignorableMiddleToolNormalized with
  | .error _ => none
  | .ok normalized =>
      some (normalized.projection.projection.decisions.length,
        normalized.occurrences.length,
        normalized.validated.final.session.nextSeq,
        normalized.occurrences.head?.map (·.event.seq.value) |>.getD 99)

def ignorableMiddleToolSourcePositions : Option (List Nat) :=
  match ignorableMiddleToolNormalized with
  | .error _ => none
  | .ok normalized =>
      some (normalized.occurrences.map NormalizedOccurrence.sourcePosition)

end Cordis.DeepSeekHarnessEventIgnorableNormalization
