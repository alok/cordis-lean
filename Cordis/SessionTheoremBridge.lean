import Cordis.SessionValidation

/-!
# Public theorem names for proof-carrying session validation

`SessionValidation` already stores the dependent transition and suffix witnesses needed to
replay a typed append or a finite raw log. This module gives the two stable theorem names used by
the v0.2 session contract without weakening those witnesses into executable booleans.
-/

namespace Cordis.Session

namespace SurfaceTransition

/-- Stable contract name for the exact replacement interval decomposition. -/
theorem replace_shadowed
    {schema : ExtensionSchema}
    {seq startSeq endSeq : Nat}
    {kind : Kind schema .surface}
    {payload : kind.Payload}
    {sourceEventSeqs : List Nat}
    {before after : List SurfaceNode}
    (transition : SurfaceTransition
      { visibility := .surface, seq, kind, payload,
        intent := .replace startSeq endSeq sourceEventSeqs }
      before after) :
    ∃ keptBefore first rest suffix,
      before = keptBefore ++ (first :: rest) ++ suffix ∧
      after = keptBefore ++ [{ seq, message := kind.surfaceMessage payload }] ++ suffix ∧
      startSeq = first.seq ∧
      endSeq = (lastNode first rest).seq :=
  replacement_exact_shadow transition

/-- Stable contract name for replacement source coverage of the shadowed interval. -/
theorem replace_covers
    {schema : ExtensionSchema}
    {seq startSeq endSeq : Nat}
    {kind : Kind schema .surface}
    {payload : kind.Payload}
    {sourceEventSeqs : List Nat}
    {before after : List SurfaceNode}
    (transition : SurfaceTransition
      { visibility := .surface, seq, kind, payload,
        intent := .replace startSeq endSeq sourceEventSeqs }
      before after) :
    ∃ keptBefore first rest suffix,
      before = keptBefore ++ (first :: rest) ++ suffix ∧
      sourceEventSeqs.Nodup ∧
      (∀ source ∈ sourceEventSeqs, source < seq) ∧
      (∀ node ∈ first :: rest, node.seq ∈ sourceEventSeqs) :=
  replacement_coverage transition

end SurfaceTransition

namespace ModelRequest

/-- A constructed request exposes only the exact session-derived values it carries. -/
theorem reconstructible
    {schema : ExtensionSchema}
    {session : Session schema}
    (request : ModelRequest session) :
    request.messages = session.messages ∧
      latestRequestHeader session.events = some request.header ∧
      request.logLength = session.events.length ∧
      request.logLength = session.nextSeq := by
  exact ⟨request.messages_eq, request.latestHeader_eq,
    request.logLength_eq, request.nextSeq_eq⟩

end ModelRequest

namespace ValidatedAppend

/-- A successful append is an intrinsic transition with the exact indexed endpoint. -/
theorem applies
    {schema : ExtensionSchema}
    {session : Session schema}
    {event : LoggedEvent schema}
    (validated : ValidatedAppend session event) :
    SurfaceTransition event session.surface validated.nextSurface ∧
      validated.apply.events = session.events ++ [event] ∧
      validated.apply.nextSeq = session.nextSeq + 1 ∧
      validated.apply.surface = validated.nextSurface ∧
      validated.apply.latestHeader = event.updateHeader session.latestHeader ∧
      ValidLog schema validated.apply.nextSeq validated.apply.events
        validated.apply.surface validated.apply.latestHeader := by
  exact ⟨validated.transition, rfl, rfl, rfl, rfl, validated.apply.valid⟩

end ValidatedAppend

namespace ValidatedLog

/-- A successful finite validation retains its intrinsic suffix and all endpoint projections. -/
theorem replays
    {schema : ExtensionSchema}
    {seed : Session schema}
    {raw : List (LoggedEvent schema)}
    (validated : ValidatedLog seed raw) :
    Nonempty (ValidatedSuffix seed raw validated.final) ∧
      validated.final.events = seed.events ++ raw ∧
      validated.final.messages = validated.final.surface.map SurfaceNode.message ∧
      ValidLog schema validated.final.nextSeq validated.final.events
        validated.final.surface validated.final.latestHeader := by
  exact ⟨⟨validated.suffix⟩, validated.events_eq,
    Session.messages_eq_surface validated.final, validated.valid⟩

end ValidatedLog

end Cordis.Session
