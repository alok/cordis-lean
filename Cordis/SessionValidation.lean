import Cordis.Session

/-!
# Proof-producing validation for typed session events

This module validates events after kind-specific payload parsing but before their surface intents
are admitted. It does not parse bytes or JSON. Successful validation returns the intrinsic proofs
needed by `Session.append`; failures retain structured evidence about the rejected claim.
-/

namespace Cordis.Session

/-- A precise reason why a typed event could not be admitted to a certified session. -/
inductive ValidationError where
  | wrongPhysicalSeq (expected actual : Nat)
  | duplicateSources (sourceEventSeqs : List Nat)
  | sourcesNotEarlier (eventSeq : Nat) (sourceEventSeqs : List Nat)
  | missingReplacementStart (startSeq : Nat)
  | missingReplacementEnd (endSeq : Nat)
  | incompleteShadowCoverage (shadowedSeqs sourceEventSeqs : List Nat)
  | producedSurfaceNotNodup (surfaceSeqs : List Nat)
  deriving DecidableEq, Repr

/-- Proofs recovered while checking the provenance list of a surface event. -/
structure SourceWitness (sourceEventSeqs : List Nat) (eventSeq : Nat) : Type where
  nodup : sourceEventSeqs.Nodup
  earlier : ∀ source ∈ sourceEventSeqs, source < eventSeq

/--
The exact nonempty contiguous surface interval selected by start and end sequence numbers.
-/
structure RangeWitness (surface : List SurfaceNode) (startSeq endSeq : Nat) where
  keptBefore : List SurfaceNode
  first : SurfaceNode
  rest : List SurfaceNode
  suffix : List SurfaceNode
  surface_eq : surface = keptBefore ++ (first :: rest) ++ suffix
  start_eq : startSeq = first.seq
  end_eq : endSeq = (lastNode first rest).seq

/-- The suffix decomposition produced after a replacement start has already been found. -/
private structure EndWitness
    (first : SurfaceNode) (tail : List SurfaceNode) (endSeq : Nat) where
  rest : List SurfaceNode
  suffix : List SurfaceNode
  tail_eq : tail = rest ++ suffix
  end_eq : endSeq = (lastNode first rest).seq

/-- Scan from a known start node until the claimed inclusive end node is found. -/
private def locateEnd
    (first : SurfaceNode) (tail : List SurfaceNode) (endSeq : Nat) :
    Except ValidationError (EndWitness first tail endSeq) :=
  if endpoint : first.seq = endSeq then
    .ok {
      rest := []
      suffix := tail
      tail_eq := by simp
      end_eq := endpoint.symm
    }
  else
    match tail with
    | [] => .error (.missingReplacementEnd endSeq)
    | next :: remaining =>
        match locateEnd next remaining endSeq with
        | .error error => .error error
        | .ok found =>
            .ok {
              rest := next :: found.rest
              suffix := found.suffix
              tail_eq := by simp [found.tail_eq]
              end_eq := found.end_eq
            }

/-- Locate a claimed nonempty contiguous replacement interval in a surface. -/
def locateRange
    (surface : List SurfaceNode) (startSeq endSeq : Nat) :
    Except ValidationError (RangeWitness surface startSeq endSeq) :=
  match surface with
  | [] => .error (.missingReplacementStart startSeq)
  | first :: tail =>
      if startsHere : first.seq = startSeq then
        match locateEnd first tail endSeq with
        | .error error => .error error
        | .ok found =>
            .ok {
              keptBefore := []
              first
              rest := found.rest
              suffix := found.suffix
              surface_eq := by simp [found.tail_eq]
              start_eq := startsHere.symm
              end_eq := found.end_eq
            }
      else
        match locateRange tail startSeq endSeq with
        | .error error => .error error
        | .ok found =>
            .ok {
              keptBefore := first :: found.keptBefore
              first := found.first
              rest := found.rest
              suffix := found.suffix
              surface_eq := by simp [found.surface_eq]
              start_eq := found.start_eq
              end_eq := found.end_eq
            }

/-- Check unique provenance references and prove that every reference precedes the new event. -/
private def validateSources (sourceEventSeqs : List Nat) (eventSeq : Nat) :
    Except ValidationError (SourceWitness sourceEventSeqs eventSeq) :=
  if nodup : sourceEventSeqs.Nodup then
    if earlier : ∀ source ∈ sourceEventSeqs, source < eventSeq then
      .ok ⟨nodup, earlier⟩
    else
      .error (.sourcesNotEarlier eventSeq sourceEventSeqs)
  else
    .error (.duplicateSources sourceEventSeqs)

/--
A successfully admitted typed event and every proof needed by the intrinsic append operation.
-/
structure ValidatedAppend
    {schema : ExtensionSchema} (session : Session schema) (event : LoggedEvent schema) where
  nextSurface : List SurfaceNode
  seq_eq : event.seq = session.nextSeq
  transition : SurfaceTransition event session.surface nextSurface
  surfaceNodup : (nextSurface.map SurfaceNode.seq).Nodup

namespace ValidatedAppend

/-- Apply exactly the intrinsic append certified by a successful validation. -/
def apply
    {schema : ExtensionSchema}
    {session : Session schema}
    {event : LoggedEvent schema}
    (validated : ValidatedAppend session event) : Session schema :=
  session.append event validated.seq_eq validated.nextSurface validated.transition
    validated.surfaceNodup

@[simp]
theorem apply_events
    {schema : ExtensionSchema}
    {session : Session schema}
    {event : LoggedEvent schema}
    (validated : ValidatedAppend session event) :
    validated.apply.events = session.events ++ [event] := rfl

@[simp]
theorem apply_surface
    {schema : ExtensionSchema}
    {session : Session schema}
    {event : LoggedEvent schema}
    (validated : ValidatedAppend session event) :
    validated.apply.surface = validated.nextSurface := rfl

end ValidatedAppend

/--
Validate one already-typed event into the intrinsic transition expected by `Session.append`.
-/
def validateAppend
    {schema : ExtensionSchema}
    (session : Session schema)
    (event : LoggedEvent schema) :
    Except ValidationError (ValidatedAppend session event) :=
  match event with
  | ⟨.logOnly, seq, kind, payload, intent⟩ =>
      if seq_eq : seq = session.nextSeq then
        .ok {
          nextSurface := session.surface
          seq_eq
          transition := SurfaceTransition.logOnly seq kind payload intent session.surface
          surfaceNodup := session.valid.surface_nodup
        }
      else
        .error (.wrongPhysicalSeq session.nextSeq seq)
  | ⟨.surface, seq, kind, payload, .append sourceEventSeqs⟩ =>
      if seq_eq : seq = session.nextSeq then
        match validateSources sourceEventSeqs seq with
        | .error error => .error error
        | .ok sources =>
            let node : SurfaceNode := { seq, message := kind.surfaceMessage payload }
            let nextSurface := session.surface ++ [node]
            if surfaceNodup : (nextSurface.map SurfaceNode.seq).Nodup then
              .ok {
                nextSurface
                seq_eq
                transition := SurfaceTransition.append seq kind payload sourceEventSeqs
                  sources.nodup sources.earlier session.surface
                surfaceNodup
              }
            else
              .error (.producedSurfaceNotNodup (nextSurface.map SurfaceNode.seq))
      else
        .error (.wrongPhysicalSeq session.nextSeq seq)
  | ⟨.surface, seq, kind, payload, .replace startSeq endSeq sourceEventSeqs⟩ =>
      if seq_eq : seq = session.nextSeq then
        match validateSources sourceEventSeqs seq with
        | .error error => .error error
        | .ok sources =>
            match locateRange session.surface startSeq endSeq with
            | .error error => .error error
            | .ok range =>
                if coversShadowed :
                    ∀ node ∈ range.first :: range.rest, node.seq ∈ sourceEventSeqs then
                  let node : SurfaceNode := { seq, message := kind.surfaceMessage payload }
                  let nextSurface := range.keptBefore ++ [node] ++ range.suffix
                  if surfaceNodup : (nextSurface.map SurfaceNode.seq).Nodup then
                    .ok {
                      nextSurface
                      seq_eq
                      transition := by
                        rw [range.surface_eq]
                        exact SurfaceTransition.replace seq kind payload startSeq endSeq
                          sourceEventSeqs range.keptBefore range.first range.rest range.suffix
                          range.start_eq range.end_eq sources.nodup sources.earlier coversShadowed
                      surfaceNodup
                    }
                  else
                    .error (.producedSurfaceNotNodup (nextSurface.map SurfaceNode.seq))
                else
                  .error (.incompleteShadowCoverage
                    ((range.first :: range.rest).map SurfaceNode.seq) sourceEventSeqs)
      else
        .error (.wrongPhysicalSeq session.nextSeq seq)

/-- A recursive certificate that a raw suffix was admitted event by event. -/
inductive ValidatedSuffix {schema : ExtensionSchema} :
    Session schema → List (LoggedEvent schema) → Session schema → Type where
  | nil (seed : Session schema) : ValidatedSuffix seed [] seed
  | cons
      {seed : Session schema}
      {event : LoggedEvent schema}
      {raw : List (LoggedEvent schema)}
      {final : Session schema}
      (head : ValidatedAppend seed event)
      (tail : ValidatedSuffix head.apply raw final) :
      ValidatedSuffix seed (event :: raw) final

namespace ValidatedSuffix

/-- Every certified suffix preserves the submitted event list exactly. -/
theorem events_eq
    {schema : ExtensionSchema}
    {seed final : Session schema}
    {raw : List (LoggedEvent schema)}
    (validated : ValidatedSuffix seed raw final) :
    final.events = seed.events ++ raw := by
  induction validated with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simpa [ValidatedAppend.apply, Session.append, List.append_assoc] using inductionHypothesis

end ValidatedSuffix

/-- A finite validated log, its final session, and its exact physical-log certificate. -/
structure ValidatedLog
    {schema : ExtensionSchema} (seed : Session schema) (raw : List (LoggedEvent schema)) where
  final : Session schema
  suffix : ValidatedSuffix seed raw final
  events_eq : final.events = seed.events ++ raw
  valid : ValidLog schema final.nextSeq final.events final.surface final.latestHeader

/-- Validate a finite suffix, threading the proof-carrying session through every event. -/
private def validateSuffix
    {schema : ExtensionSchema}
    (seed : Session schema)
    (raw : List (LoggedEvent schema)) :
    Except ValidationError (Σ final : Session schema, ValidatedSuffix seed raw final) :=
  match raw with
  | [] => .ok ⟨seed, .nil seed⟩
  | event :: rest =>
      match validateAppend seed event with
      | .error error => .error error
      | .ok head =>
          match validateSuffix head.apply rest with
          | .error error => .error error
          | .ok ⟨final, tail⟩ => .ok ⟨final, .cons head tail⟩

/-- Validate a finite typed event list and retain its entire intrinsic `ValidLog` proof. -/
def validateLog
    {schema : ExtensionSchema}
    (seed : Session schema)
    (raw : List (LoggedEvent schema)) :
    Except ValidationError (ValidatedLog seed raw) :=
  match validateSuffix seed raw with
  | .error error => .error error
  | .ok ⟨final, suffix⟩ =>
      .ok {
        final
        suffix
        events_eq := suffix.events_eq
        valid := final.valid
      }

/-! ## Certified executable examples -/

/-- Revalidation of the intrinsic replacement example reaches the same message view. -/
theorem replacementEvent_revalidates :
    match validateAppend certifiedSession replacementEvent with
    | .error _ => False
    | .ok validated => validated.apply.messages = replacementSession.messages := by
  rfl

def wrongSequenceEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 99
  kind := .userMessage
  payload := { content := "late" }
  intent := .append []

theorem wrongSequenceEvent_rejected :
    validateAppend certifiedSession wrongSequenceEvent =
      .error (.wrongPhysicalSeq 5 99) := by
  rfl

def missingStartEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 5
  kind := .assistantMessage
  payload := { turn := 0, step := 0, content := "bad start", rawToolCalls := [] }
  intent := .replace 99 4 [2, 4]

theorem missingStartEvent_rejected :
    validateAppend certifiedSession missingStartEvent =
      .error (.missingReplacementStart 99) := by
  rfl

def missingEndEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 5
  kind := .assistantMessage
  payload := { turn := 0, step := 0, content := "bad end", rawToolCalls := [] }
  intent := .replace 2 99 [2, 4]

theorem missingEndEvent_rejected :
    validateAppend certifiedSession missingEndEvent =
      .error (.missingReplacementEnd 99) := by
  rfl

def incompleteCoverageEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 5
  kind := .assistantMessage
  payload := { turn := 0, step := 0, content := "bad coverage", rawToolCalls := [] }
  intent := .replace 2 4 [2]

theorem incompleteCoverageEvent_rejected :
    validateAppend certifiedSession incompleteCoverageEvent =
      .error (.incompleteShadowCoverage [2, 4] [2]) := by
  rfl

def shortRawLog : List (LoggedEvent noExtensions) := [headerEvent, userEvent]

theorem shortRawLog_validates :
    match validateLog (Session.empty noExtensions) shortRawLog with
    | .error _ => False
    | .ok validated =>
        validated.final.events = shortRawLog ∧
        validated.final.messages = [.user "What is the answer?"] := by
  simp [validateLog, validateSuffix, shortRawLog, validateAppend, validateSources,
    ValidatedAppend.apply, Session.append, Session.empty, headerEvent, userEvent,
    Session.messages, deriveMessages]

end Cordis.Session
