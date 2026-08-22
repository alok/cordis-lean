import Cordis.DeepSeekHarnessExtensions

/-!
# Core-session lifting into an arbitrary extension schema

The core `SessionRefinement` decoder is intentionally indexed by `Session.noExtensions`:
its accepted JSON rows are the current source-honest core subset.  An extension schema can
still host that validated core session without weakening any dependent payload, intent, or
surface-transition proof.  This module gives that transport explicitly.

`liftSession` maps only core constructors.  It preserves sequence numbers, the materialized
surface, request-header state, every `ValidLog` transition, and the structural protocol
projection.  The result is therefore a genuine arbitrary-schema core session, not a claim that
arbitrary extension JSON has been decoded or that extension rows have been interleaved into one
replayed model.  Mixed source partitioning remains the separate boundary in
`DeepSeekHarnessMixedPersistence`.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessSchemaLift

open Cordis

/-! ## Constructor-indexed transport -/

/-- Map a core kind into the same core constructor of a target schema. -/
def liftKind {schema : Session.ExtensionSchema} {visibility : Session.Visibility}
    (kind : Session.Kind Session.noExtensions visibility) : Session.Kind schema visibility :=
  match kind with
  | .turnStart => .turnStart
  | .turnEnd => .turnEnd
  | .stepStart => .stepStart
  | .stepEnd => .stepEnd
  | .userMessage => .userMessage
  | .requestHeader => .requestHeader
  | .todoWrite => .todoWrite
  | .requestContext => .requestContext
  | .sessionEndSeed => .sessionEndSeed
  | .assistantChunk => .assistantChunk
  | .assistantReasoning => .assistantReasoning
  | .assistantMessage => .assistantMessage
  | .toolCall => .toolCall
  | .toolResult => .toolResult
  | .custom kind => nomatch kind

/-- Core payloads are schema-independent after the kind index has been transported. -/
def liftPayload {schema : Session.ExtensionSchema} {visibility : Session.Visibility}
    (kind : Session.Kind Session.noExtensions visibility) :
    kind.Payload → (liftKind (schema := schema) kind).Payload := by
  cases kind with
  | turnStart => intro payload; exact payload
  | turnEnd => intro payload; exact payload
  | stepStart => intro payload; exact payload
  | stepEnd => intro payload; exact payload
  | userMessage => intro payload; exact payload
  | requestHeader => intro payload; exact payload
  | todoWrite => intro payload; exact payload
  | requestContext => intro payload; exact payload
  | sessionEndSeed => intro payload; exact payload
  | assistantChunk => intro payload; exact payload
  | assistantReasoning => intro payload; exact payload
  | assistantMessage => intro payload; exact payload
  | toolCall => intro payload; exact payload
  | toolResult => intro payload; exact payload
  | custom kind => exact nomatch kind

/-- Transport the intent index; log-only intents normalize to the unique token. -/
def liftIntent {schema : Session.ExtensionSchema} {visibility : Session.Visibility}
    (kind : Session.Kind Session.noExtensions visibility) :
    Session.EventIntent kind → Session.EventIntent (liftKind (schema := schema) kind) := by
  cases kind with
  | turnStart => intro intent; exact intent
  | turnEnd => intro intent; exact intent
  | stepStart => intro intent; exact intent
  | stepEnd => intro intent; exact intent
  | userMessage => intro intent; exact intent
  | requestHeader => intro intent; exact intent
  | todoWrite => intro intent; exact intent
  | requestContext => intro intent; exact intent
  | sessionEndSeed => intro intent; exact intent
  | assistantChunk => intro intent; exact intent
  | assistantReasoning => intro intent; exact intent
  | assistantMessage => intro intent; exact intent
  | toolCall => intro intent; exact intent
  | toolResult => intro intent; exact intent
  | custom kind => exact nomatch kind

/-- Lift one core event while retaining its sequence, payload, visibility, and intent. -/
def liftEvent {schema : Session.ExtensionSchema}
    (event : Session.LoggedEvent Session.noExtensions) : Session.LoggedEvent schema where
  visibility := event.visibility
  seq := event.seq
  kind := liftKind (schema := schema) event.kind
  payload := liftPayload (schema := schema) event.kind event.payload
  intent := liftIntent (schema := schema) event.kind event.intent

/-- Core protocol observations are invariant under schema lifting. -/
theorem liftEvent_protocol {schema : Session.ExtensionSchema}
    (event : Session.LoggedEvent Session.noExtensions) :
    Session.LoggedEvent.protocolEvent? (schema := schema) (liftEvent (schema := schema) event) =
      Session.LoggedEvent.protocolEvent? (schema := Session.noExtensions) event := by
  cases event with
  | mk visibility seq kind payload intent =>
      cases kind with
      | turnStart => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | turnEnd => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | stepStart => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | stepEnd => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | userMessage => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | requestHeader => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | todoWrite => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | requestContext => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | sessionEndSeed => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | assistantChunk => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | assistantReasoning => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | assistantMessage => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | toolCall => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | toolResult => simp [liftEvent, liftKind, liftPayload, liftIntent]
      | custom kind => exact nomatch kind

/-- Schema lifting does not change physical sequence numbers. -/
theorem liftEvent_seq {schema : Session.ExtensionSchema}
    (event : Session.LoggedEvent Session.noExtensions) :
    (liftEvent (schema := schema) event).seq = event.seq := by
  rfl

/-- The surface message selected by a core kind is unchanged by lifting. -/
theorem liftKind_surfaceMessage {schema : Session.ExtensionSchema}
    {kind : Session.Kind Session.noExtensions .surface} (payload : kind.Payload) :
    (liftKind (schema := schema) kind).surfaceMessage
        (liftPayload (schema := schema) kind payload) = kind.surfaceMessage payload := by
  cases kind with
  | userMessage => simp [liftKind, liftPayload]
  | assistantMessage => simp [liftKind, liftPayload]
  | toolResult => simp [liftKind, liftPayload]
  | custom kind => exact nomatch kind

theorem liftEvent_logOnly {schema : Session.ExtensionSchema}
    {seq : Nat} {kind : Session.Kind Session.noExtensions .logOnly}
    {payload : kind.Payload} (intent : Session.EventIntent kind) :
    liftEvent (schema := schema)
        { visibility := .logOnly, seq, kind, payload, intent } =
      { visibility := .logOnly, seq, kind := liftKind (schema := schema) kind
        payload := liftPayload (schema := schema) kind payload
        intent := .token } := by
  cases kind <;> cases intent <;> rfl

theorem liftEvent_append {schema : Session.ExtensionSchema}
    {seq : Nat} {kind : Session.Kind Session.noExtensions .surface}
    {payload : kind.Payload} {sources : List Nat} :
    liftEvent (schema := schema)
        { visibility := .surface, seq, kind, payload,
          intent := .append sources } =
      { visibility := .surface, seq, kind := liftKind (schema := schema) kind
        payload := liftPayload (schema := schema) kind payload
        intent := .append sources } := by
  cases kind with
  | userMessage => rfl
  | assistantMessage => rfl
  | toolResult => rfl
  | custom kind => exact nomatch kind

theorem liftEvent_replace {schema : Session.ExtensionSchema}
    {seq startSeq endSeq : Nat} {kind : Session.Kind Session.noExtensions .surface}
    {payload : kind.Payload} {sources : List Nat} :
    liftEvent (schema := schema)
        { visibility := .surface, seq, kind, payload,
          intent := .replace startSeq endSeq sources } =
      { visibility := .surface, seq, kind := liftKind (schema := schema) kind
        payload := liftPayload (schema := schema) kind payload
        intent := .replace startSeq endSeq sources } := by
  cases kind with
  | userMessage => rfl
  | assistantMessage => rfl
  | toolResult => rfl
  | custom kind => exact nomatch kind

/-- Header snapshots are unchanged because only the core request-header constructor is lifted. -/
theorem liftEvent_updateHeader {schema : Session.ExtensionSchema}
    (event : Session.LoggedEvent Session.noExtensions) (header : Option Session.RequestHeader) :
    (liftEvent (schema := schema) event).updateHeader header = event.updateHeader header := by
  cases event with
  | mk visibility seq kind payload intent =>
      cases kind with
      | turnStart => rfl
      | turnEnd => rfl
      | stepStart => rfl
      | stepEnd => rfl
      | userMessage => rfl
      | requestHeader => rfl
      | todoWrite => rfl
      | requestContext => rfl
      | sessionEndSeed => rfl
      | assistantChunk => rfl
      | assistantReasoning => rfl
      | assistantMessage => rfl
      | toolCall => rfl
      | toolResult => rfl
      | custom kind => exact nomatch kind

/-! ## Valid-log and session transport -/

/-- Every validated core surface transition lifts to the same transition in the target schema. -/
theorem liftTransition {schema : Session.ExtensionSchema}
    {event : Session.LoggedEvent Session.noExtensions}
    {before after : List Session.SurfaceNode}
    (transition : Session.SurfaceTransition event before after) :
    Session.SurfaceTransition (liftEvent (schema := schema) event) before after := by
  cases transition with
  | logOnly seq kind payload intent =>
      rw [liftEvent_logOnly]
      exact .logOnly seq (liftKind (schema := schema) kind)
        (liftPayload (schema := schema) kind payload) .token before
  | append seq kind payload sources nodup earlier =>
      rw [liftEvent_append]
      rw [← liftKind_surfaceMessage (schema := schema) (kind := kind) payload]
      exact .append seq (liftKind (schema := schema) kind)
        (liftPayload (schema := schema) kind payload) sources nodup earlier before
  | replace seq kind payload startSeq endSeq sources keptBefore first rest suffix start_eq end_eq
      nodup earlier covers =>
      rw [liftEvent_replace]
      rw [← liftKind_surfaceMessage (schema := schema) (kind := kind) payload]
      exact .replace seq (liftKind (schema := schema) kind)
        (liftPayload (schema := schema) kind payload) startSeq endSeq sources
        keptBefore first rest suffix start_eq end_eq nodup earlier covers

/-- A `ValidLog` proof is transported without changing its event list's physical indices. -/
theorem liftValidLog {schema : Session.ExtensionSchema}
    {nextSeq : Nat} {events : List (Session.LoggedEvent Session.noExtensions)}
    {surface : List Session.SurfaceNode} {header : Option Session.RequestHeader}
    (valid : Session.ValidLog Session.noExtensions nextSeq events surface header) :
    Session.ValidLog schema nextSeq (events.map liftEvent) surface header := by
  induction valid with
  | empty => exact .empty
  | @snoc nextSeq events surface nextSurface header valid event seq_eq transition nodup ih =>
      simpa [List.map_append, liftEvent_updateHeader] using
        (Session.ValidLog.snoc ih (liftEvent event)
          (by rw [liftEvent_seq]; exact seq_eq)
          (liftTransition transition) nodup)

/-- Lift a complete core session into any extension schema. -/
def liftSession {schema : Session.ExtensionSchema}
    (session : Session.Session Session.noExtensions) : Session.Session schema where
  nextSeq := session.nextSeq
  events := session.events.map liftEvent
  surface := session.surface
  latestHeader := session.latestHeader
  valid := liftValidLog session.valid

theorem liftSession_nextSeq {schema : Session.ExtensionSchema}
    (session : Session.Session Session.noExtensions) :
    (liftSession (schema := schema) session).nextSeq = session.nextSeq := by
  rfl

theorem liftSession_surface {schema : Session.ExtensionSchema}
    (session : Session.Session Session.noExtensions) :
    (liftSession (schema := schema) session).surface = session.surface := by
  rfl

theorem liftSession_latestHeader {schema : Session.ExtensionSchema}
    (session : Session.Session Session.noExtensions) :
    (liftSession (schema := schema) session).latestHeader = session.latestHeader := by
  rfl

theorem liftSession_protocolProjection {schema : Session.ExtensionSchema}
    (session : Session.Session Session.noExtensions) :
    Session.protocolProjection (schema := schema) (liftSession (schema := schema) session).events =
      Session.protocolProjection (schema := Session.noExtensions) session.events := by
  change List.filterMap Session.LoggedEvent.protocolEvent?
      (session.events.map (liftEvent (schema := schema))) =
    List.filterMap Session.LoggedEvent.protocolEvent? session.events
  induction session.events with
  | nil => rfl
  | cons event events ih =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [liftEvent_protocol]
      rw [ih]

/-! ## Certificate packaging and executable example -/

/-- The source and target endpoints of one schema lift, with all principal laws retained. -/
structure SchemaLiftCertificate
    {schema : Session.ExtensionSchema}
    (source : Session.Session Session.noExtensions) where
  target : Session.Session schema
  target_eq : target = liftSession (schema := schema) source
  target_valid : Session.ValidLog schema target.nextSeq target.events target.surface
    target.latestHeader
  nextSeq_eq : target.nextSeq = source.nextSeq
  surface_eq : target.surface = source.surface
  header_eq : target.latestHeader = source.latestHeader
  protocol_eq : Session.protocolProjection target.events =
    Session.protocolProjection source.events

/-- Build the proof-carrying arbitrary-schema core endpoint. -/
def certify
    {schema : Session.ExtensionSchema}
    (source : Session.Session Session.noExtensions) :
    SchemaLiftCertificate (schema := schema) source where
  target := liftSession (schema := schema) source
  target_eq := rfl
  target_valid := (liftSession (schema := schema) source).valid
  nextSeq_eq := liftSession_nextSeq source
  surface_eq := liftSession_surface source
  header_eq := liftSession_latestHeader source
  protocol_eq := liftSession_protocolProjection source

namespace Example

open DeepSeekHarnessExtensions

def liftedCertifiedSession : Session.Session exampleSchema :=
  liftSession (schema := exampleSchema) Session.certifiedSession

def certifiedLift : SchemaLiftCertificate (schema := exampleSchema) Session.certifiedSession :=
  certify Session.certifiedSession

theorem certifiedLift_summary :
    (certifiedLift.target.nextSeq, certifiedLift.target.surface.length,
      certifiedLift.target.latestHeader.isSome) = (5, 3, true) := by
  rfl

theorem certifiedLift_protocol_exact :
    Session.protocolProjection certifiedLift.target.events =
      Session.certifiedToolTrace.erase :=
  certifiedLift.protocol_eq.trans Session.certifiedSession_protocolProjection

theorem lifted_extension_schema_is_not_custom :
    liftedCertifiedSession.events.all (fun event =>
      match event.kind with
      | .custom _ => false
      | _ => true) = true := by
  rfl

end Example

end Cordis.DeepSeekHarnessSchemaLift
