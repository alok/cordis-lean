import Cordis.Protocol

/-!
# Proof-carrying append-only session logs

This module models the persistent session log as the source of truth. Surface messages and the
latest request header are materialized views whose exact relationship to the log is witnessed by
`ValidLog`. Event visibility, payloads, and surface intents are indexed so that log-only events
cannot accidentally carry a surface mutation.
-/

namespace Cordis.Session

/-- A complete raw tool call retained on assistant messages and tool-call events. -/
structure ToolCall where
  id : CallId
  name : String
  arguments : String
  deriving DecidableEq, Repr

/-- The three message forms presented to a model. -/
inductive Message where
  | user (content : String)
  | assistant (content : String) (rawToolCalls : List ToolCall)
  | toolResult (callId : CallId) (content : String) (isError : Bool)
  deriving DecidableEq, Repr

/-- Descriptive schema for one tool in a model request. -/
structure ToolSchema where
  name : String
  description : String
  inputSchema : String
  deriving DecidableEq, Repr

/-- The full provider request snapshot reconstructed from the latest header event. -/
structure RequestHeader where
  provider : String
  model : String
  system : Option String
  toolSchemas : List ToolSchema
  deriving DecidableEq, Repr

/-- One item in the log-only whole-list todo snapshot. -/
inductive TodoStatus where
  | pending
  | inProgress
  | completed
  deriving DecidableEq, Repr

structure TodoItem where
  content : String
  status : TodoStatus
  deriving DecidableEq, Repr

structure TodoWritePayload where
  todos : List TodoItem
  deriving DecidableEq, Repr

/-- Route metadata logged separately from the full request header. -/
structure RequestContext where
  provider : String
  model : String
  contextWindow : Option Nat
  deriving DecidableEq, Repr

/-- The seed boundary carries meaning in its sequence position, not its payload. -/
structure SessionEndSeedPayload where
  deriving DecidableEq, Repr

/-- Why a harness turn stopped. -/
inductive TurnEndReason where
  | completed
  | maxTokens
  | requestedTools
  | cancelled
  | failed (detail : String)
  deriving DecidableEq, Repr

structure TurnStartPayload where
  turn : Nat
  deriving DecidableEq, Repr

structure TurnEndPayload where
  turn : Nat
  nextStep : Nat
  reason : TurnEndReason
  deriving DecidableEq, Repr

structure StepStartPayload where
  turn : Nat
  step : Nat
  deriving DecidableEq, Repr

structure StepEndPayload where
  turn : Nat
  step : Nat
  deriving DecidableEq, Repr

structure UserMessagePayload where
  content : String
  deriving DecidableEq, Repr

structure AssistantChunkPayload where
  turn : Nat
  step : Nat
  delta : String
  deriving DecidableEq, Repr

structure AssistantMessagePayload where
  turn : Nat
  step : Nat
  content : String
  rawToolCalls : List ToolCall
  deriving DecidableEq, Repr

structure ToolCallEventPayload where
  turn : Nat
  step : Nat
  call : ToolCall
  deriving DecidableEq, Repr

structure ToolResultPayload where
  turn : Nat
  step : Nat
  callId : CallId
  content : String
  isError : Bool
  deriving DecidableEq, Repr

/-- Whether an event exists only in the log or also changes the model-facing surface. -/
inductive Visibility where
  | logOnly
  | surface
  deriving DecidableEq, Repr

/--
An application-defined extension event universe. Visibility is an index of `Kind`; every kind
selects its exact payload, while surface kinds must additionally provide a message projection.
-/
structure ExtensionSchema where
  Kind : Visibility → Type
  Payload : {visibility : Visibility} → Kind visibility → Type
  surfaceContent : (kind : Kind .surface) → Payload kind → Message

/-- An extension schema with no custom events. -/
def noExtensions : ExtensionSchema where
  Kind := fun _ => Empty
  Payload := fun kind => nomatch kind
  surfaceContent := fun kind => nomatch kind

/-- Core event kinds, indexed by whether they may mutate the model-facing surface. -/
inductive Kind (schema : ExtensionSchema) : Visibility → Type where
  | turnStart : Kind schema .logOnly
  | turnEnd : Kind schema .logOnly
  | stepStart : Kind schema .logOnly
  | stepEnd : Kind schema .logOnly
  | userMessage : Kind schema .surface
  | requestHeader : Kind schema .logOnly
  | todoWrite : Kind schema .logOnly
  | requestContext : Kind schema .logOnly
  | sessionEndSeed : Kind schema .logOnly
  | assistantChunk : Kind schema .logOnly
  | assistantMessage : Kind schema .surface
  | toolCall : Kind schema .logOnly
  | toolResult : Kind schema .surface
  | custom {visibility : Visibility} (kind : schema.Kind visibility) : Kind schema visibility

namespace Kind

/-- The exact payload selected by a core or extension event kind. -/
@[simp] def Payload {schema : ExtensionSchema} :
    {visibility : Visibility} → Kind schema visibility → Type
  | _, .turnStart => TurnStartPayload
  | _, .turnEnd => TurnEndPayload
  | _, .stepStart => StepStartPayload
  | _, .stepEnd => StepEndPayload
  | _, .userMessage => UserMessagePayload
  | _, .requestHeader => RequestHeader
  | _, .todoWrite => TodoWritePayload
  | _, .requestContext => RequestContext
  | _, .sessionEndSeed => SessionEndSeedPayload
  | _, .assistantChunk => AssistantChunkPayload
  | _, .assistantMessage => AssistantMessagePayload
  | _, .toolCall => ToolCallEventPayload
  | _, .toolResult => ToolResultPayload
  | _, .custom kind => schema.Payload kind

/-- The total message projection for a surface-visible kind. -/
@[simp] def surfaceMessage {schema : ExtensionSchema} :
    (kind : Kind schema .surface) → kind.Payload → Message
  | .userMessage, payload => .user payload.content
  | .assistantMessage, payload => .assistant payload.content payload.rawToolCalls
  | .toolResult, payload => .toolResult payload.callId payload.content payload.isError
  | .custom kind, payload => schema.surfaceContent kind payload

/-- Project an arbitrary event payload to the optional surface message it contributes. -/
def projectMessage {schema : ExtensionSchema} :
    {visibility : Visibility} → (kind : Kind schema visibility) →
      kind.Payload → Option Message
  | _, .turnStart, _ => none
  | _, .turnEnd, _ => none
  | _, .stepStart, _ => none
  | _, .stepEnd, _ => none
  | _, .userMessage, payload => some (.user payload.content)
  | _, .requestHeader, _ => none
  | _, .todoWrite, _ => none
  | _, .requestContext, _ => none
  | _, .sessionEndSeed, _ => none
  | _, .assistantChunk, _ => none
  | _, .assistantMessage, payload => some (.assistant payload.content payload.rawToolCalls)
  | _, .toolCall, _ => none
  | _, .toolResult, payload => some (.toolResult payload.callId payload.content payload.isError)
  | .logOnly, .custom _, _ => none
  | .surface, .custom kind, payload => some (schema.surfaceContent kind payload)

/-- Select a complete request header exactly for the request-header kind. -/
@[simp] def projectHeader {schema : ExtensionSchema} :
    {visibility : Visibility} → (kind : Kind schema visibility) →
      kind.Payload → Option RequestHeader
  | _, .requestHeader, payload => some payload
  | _, _, _ => none

end Kind

/-- A surface edit and the exact earlier events from which it was derived. -/
inductive SurfaceIntent where
  | append (sourceEventSeqs : List Nat)
  | replace (startSeq endSeq : Nat) (sourceEventSeqs : List Nat)
  deriving DecidableEq, Repr

/-- The unique intent token carried by log-only events. -/
inductive NoSurfaceIntent where
  | token
  deriving DecidableEq, Repr

/--
The intent type selected by an event kind. It reduces to a singleton for log-only kinds and to
`SurfaceIntent` for surface kinds.
-/
def EventIntent {schema : ExtensionSchema} {visibility : Visibility}
    (_kind : Kind schema visibility) : Type :=
  match visibility with
  | .logOnly => NoSurfaceIntent
  | .surface => SurfaceIntent

/-- One append-only log event with payload and intent fixed by its kind. -/
structure LoggedEvent (schema : ExtensionSchema) where
  visibility : Visibility
  seq : Nat
  kind : Kind schema visibility
  payload : kind.Payload
  intent : EventIntent kind

namespace LoggedEvent

/-- The optional message contributed by an event before its surface intent is interpreted. -/
def surfaceMessage {schema : ExtensionSchema} (event : LoggedEvent schema) : Option Message :=
  event.kind.projectMessage event.payload

/-- Update the latest request snapshot with one event. -/
def updateHeader {schema : ExtensionSchema}
    (event : LoggedEvent schema) (current : Option RequestHeader) : Option RequestHeader :=
  match Kind.projectHeader event.kind event.payload with
  | some header => some header
  | none => current

/-- Project the rich log onto the structural protocol checked by `Cordis.Protocol`. -/
@[simp] def protocolEvent? {schema : ExtensionSchema}
    (event : LoggedEvent schema) : Option RuntimeEvent :=
  match event.visibility, event.kind, event.payload with
  | _, .turnStart, payload => some (.turnStart payload.turn)
  | _, .turnEnd, payload => some (.turnEnd payload.turn payload.nextStep)
  | _, .stepStart, payload => some (.stepStart payload.turn payload.step)
  | _, .stepEnd, payload => some (.stepEnd payload.turn payload.step)
  | _, .toolCall, payload =>
      some (.toolCall payload.turn payload.step payload.call.id)
  | _, .toolResult, payload =>
      some (.toolResult payload.turn payload.step payload.callId)
  | _, _, _ => none

end LoggedEvent

/-- Fold the append-only log to its latest complete request-header snapshot. -/
def latestRequestHeader {schema : ExtensionSchema}
    (events : List (LoggedEvent schema)) : Option RequestHeader :=
  events.foldl (fun current event => event.updateHeader current) none

/-- Structural protocol events are derived from the canonical rich log. -/
def protocolProjection {schema : ExtensionSchema}
    (events : List (LoggedEvent schema)) : List RuntimeEvent :=
  events.filterMap LoggedEvent.protocolEvent?

/-- One materialized surface node remembers the event that created it. -/
structure SurfaceNode where
  seq : Nat
  message : Message
  deriving DecidableEq, Repr

/-- The last node of a nonempty list represented by its first node and remaining tail. -/
def lastNode (first : SurfaceNode) : List SurfaceNode → SurfaceNode
  | [] => first
  | next :: rest => lastNode next rest

/-- Model messages are exactly the messages stored by the validated surface view. -/
def deriveMessages (surface : List SurfaceNode) : List Message :=
  surface.map SurfaceNode.message

/--
An intrinsic proof that one append-only event performs its claimed surface transition.

Replacement stores the actual prefix, nonempty shadowed interval, and suffix in the indices. Its
source references are unique, earlier than the replacing event, and cover every shadowed node.
-/
inductive SurfaceTransition {schema : ExtensionSchema} :
    LoggedEvent schema → List SurfaceNode → List SurfaceNode → Prop where
  | logOnly
      (seq : Nat)
      (kind : Kind schema .logOnly)
      (payload : kind.Payload)
      (intent : EventIntent kind)
      (surface : List SurfaceNode) :
      SurfaceTransition
        { visibility := .logOnly, seq, kind, payload, intent }
        surface
        surface
  | append
      (seq : Nat)
      (kind : Kind schema .surface)
      (payload : kind.Payload)
      (sourceEventSeqs : List Nat)
      (sourcesNodup : sourceEventSeqs.Nodup)
      (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < seq)
      (surface : List SurfaceNode) :
      SurfaceTransition
        { visibility := .surface, seq, kind, payload,
          intent := .append sourceEventSeqs }
        surface
        (surface ++ [{ seq, message := kind.surfaceMessage payload }])
  | replace
      (seq : Nat)
      (kind : Kind schema .surface)
      (payload : kind.Payload)
      (startSeq endSeq : Nat)
      (sourceEventSeqs : List Nat)
      (keptBefore : List SurfaceNode)
      (first : SurfaceNode)
      (rest suffix : List SurfaceNode)
      (start_eq : startSeq = first.seq)
      (end_eq : endSeq = (lastNode first rest).seq)
      (sourcesNodup : sourceEventSeqs.Nodup)
      (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < seq)
      (coversShadowed : ∀ node ∈ first :: rest, node.seq ∈ sourceEventSeqs) :
      SurfaceTransition
        { visibility := .surface, seq, kind, payload,
          intent := .replace startSeq endSeq sourceEventSeqs }
        (keptBefore ++ (first :: rest) ++ suffix)
        (keptBefore ++ [{ seq, message := kind.surfaceMessage payload }] ++ suffix)

namespace SurfaceTransition

/-- A replacement transition exposes the exact interval it shadows. -/
theorem replacement_exact_shadow
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
      endSeq = (lastNode first rest).seq := by
  cases transition with
  | replace _ _ _ _ _ _ keptBefore first rest suffix start_eq end_eq _ _ _ =>
      exact ⟨keptBefore, first, rest, suffix, rfl, rfl, start_eq, end_eq⟩

/-- Every node shadowed by a replacement is covered by one of its unique source references. -/
theorem replacement_coverage
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
      (∀ node ∈ first :: rest, node.seq ∈ sourceEventSeqs) := by
  cases transition with
  | replace _ _ _ _ _ _ keptBefore first rest suffix _ _ nodup earlier covers =>
      exact ⟨keptBefore, first, rest, suffix, rfl, nodup, earlier, covers⟩

/-- A surface transition never introduces a node sequenced after its event. -/
theorem references_at_most
    {schema : ExtensionSchema}
    {event : LoggedEvent schema}
    {before after : List SurfaceNode}
    (transition : SurfaceTransition event before after)
    (beforeEarlier : ∀ node ∈ before, node.seq < event.seq) :
    ∀ node ∈ after, node.seq ≤ event.seq := by
  cases transition with
  | logOnly seq kind payload intent surface =>
      intro node member
      exact Nat.le_of_lt (beforeEarlier node member)
  | append seq kind payload sources nodup earlier surface =>
      intro node member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact Nat.le_of_lt (beforeEarlier node member)
      · exact Nat.le_refl seq
  | replace seq kind payload startSeq endSeq sources keptBefore first rest suffix start_eq end_eq
      nodup earlier covers =>
      intro node member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with (member | rfl) | member
      · exact Nat.le_of_lt (beforeEarlier node (by simp [member]))
      · exact Nat.le_refl seq
      · exact Nat.le_of_lt (beforeEarlier node (by simp [member]))

end SurfaceTransition

/-- Sequence numbers extracted from the physical log. -/
def eventSeqs {schema : ExtensionSchema} (events : List (LoggedEvent schema)) : List Nat :=
  events.map LoggedEvent.seq

/--
An append-oriented proof that a physical event list and its materialized views are exact.
-/
inductive ValidLog (schema : ExtensionSchema) :
    Nat → List (LoggedEvent schema) → List SurfaceNode → Option RequestHeader → Prop where
  | empty : ValidLog schema 0 [] [] none
  | snoc
      {nextSeq : Nat}
      {events : List (LoggedEvent schema)}
      {surface nextSurface : List SurfaceNode}
      {header : Option RequestHeader}
      (valid : ValidLog schema nextSeq events surface header)
      (event : LoggedEvent schema)
      (seq_eq : event.seq = nextSeq)
      (transition : SurfaceTransition event surface nextSurface)
      (surfaceNodup : (nextSurface.map SurfaceNode.seq).Nodup) :
      ValidLog schema (nextSeq + 1) (events ++ [event]) nextSurface
        (event.updateHeader header)

namespace ValidLog

/-- Physical log length is the next contiguous sequence number. -/
theorem length_eq_nextSeq
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (valid : ValidLog schema nextSeq events surface header) :
    events.length = nextSeq := by
  induction valid with
  | empty => rfl
  | snoc valid event seq_eq transition surfaceNodup inductionHypothesis =>
      simp [inductionHypothesis]

/-- Physical event sequence numbers are exactly `0, 1, ..., nextSeq - 1`. -/
theorem seqs_eq_range
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (valid : ValidLog schema nextSeq events surface header) :
    eventSeqs events = List.range nextSeq := by
  induction valid with
  | empty => rfl
  | snoc valid event seq_eq transition surfaceNodup inductionHypothesis =>
      simp only [eventSeqs] at inductionHypothesis ⊢
      simp [inductionHypothesis, seq_eq, List.range_succ]

/-- A validated materialized surface never contains the same event sequence twice. -/
theorem surface_nodup
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (valid : ValidLog schema nextSeq events surface header) :
    (surface.map SurfaceNode.seq).Nodup := by
  cases valid with
  | empty => exact List.nodup_nil
  | snoc valid event seq_eq transition surfaceNodup => exact surfaceNodup

/-- Every materialized surface node references an earlier physical event. -/
theorem surface_references_earlier
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (valid : ValidLog schema nextSeq events surface header) :
    ∀ node ∈ surface, node.seq < nextSeq := by
  induction valid with
  | empty => simp
  | @snoc nextSeq events surface nextSurface header valid event seq_eq transition surfaceNodup
      inductionHypothesis =>
      intro node member
      have beforeEarlier : ∀ prior ∈ surface, prior.seq < event.seq := by
        intro prior priorMember
        simpa [seq_eq] using inductionHypothesis prior priorMember
      have atMost := transition.references_at_most beforeEarlier node member
      calc
        node.seq ≤ event.seq := atMost
        _ = nextSeq := seq_eq
        _ < nextSeq + 1 := Nat.lt_succ_self nextSeq

/-- The stored header is exactly the latest request-header event in the physical log. -/
theorem latest_header_eq
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (valid : ValidLog schema nextSeq events surface header) :
    latestRequestHeader events = header := by
  induction valid with
  | empty => rfl
  | snoc valid event seq_eq transition surfaceNodup inductionHypothesis =>
      simp only [latestRequestHeader] at inductionHypothesis ⊢
      simp [List.foldl_append, inductionHypothesis]

/-- The model-message derivation is definitionally the surface projection. -/
theorem messages_eq_surface
    {schema : ExtensionSchema}
    {nextSeq : Nat}
    {events : List (LoggedEvent schema)}
    {surface : List SurfaceNode}
    {header : Option RequestHeader}
    (_valid : ValidLog schema nextSeq events surface header) :
    deriveMessages surface = surface.map SurfaceNode.message := rfl

end ValidLog

/-- A session packages an append-only log with all of its exact derived-state certificates. -/
structure Session (schema : ExtensionSchema) where
  nextSeq : Nat
  events : List (LoggedEvent schema)
  surface : List SurfaceNode
  latestHeader : Option RequestHeader
  valid : ValidLog schema nextSeq events surface latestHeader

/-- A rich session whose structural projection is one intrinsic protocol trace. -/
structure ProtocolCertificate
    {schema : ExtensionSchema}
    (session : Session schema)
    (start finish : SessionState) where
  trace : Trace start finish
  projection_eq : protocolProjection session.events = trace.erase

namespace ProtocolCertificate

/-- The structural projection of a certified rich session replays to its indexed endpoint. -/
theorem replays
    {schema : ExtensionSchema}
    {session : Session schema}
    {start finish : SessionState}
    (certificate : ProtocolCertificate session start finish) :
    replayRaw (eraseState start) (protocolProjection session.events) =
      .ok (eraseState finish) := by
  rw [certificate.projection_eq]
  exact replayRaw_eraseTrace certificate.trace

end ProtocolCertificate

namespace Session

/-- The unique empty certified session. -/
def empty (schema : ExtensionSchema) : Session schema where
  nextSeq := 0
  events := []
  surface := []
  latestHeader := none
  valid := .empty

/-- Append one intrinsically certified event and update every exact materialized view. -/
def append
    {schema : ExtensionSchema}
    (session : Session schema)
    (event : LoggedEvent schema)
    (seq_eq : event.seq = session.nextSeq)
    (nextSurface : List SurfaceNode)
    (transition : SurfaceTransition event session.surface nextSurface)
    (surfaceNodup : (nextSurface.map SurfaceNode.seq).Nodup) : Session schema where
  nextSeq := session.nextSeq + 1
  events := session.events ++ [event]
  surface := nextSurface
  latestHeader := event.updateHeader session.latestHeader
  valid := .snoc session.valid event seq_eq transition surfaceNodup

/-- Append a log-only event; surface metadata is absent by the kind's index. -/
def appendLogOnly
    {schema : ExtensionSchema}
    (session : Session schema)
    (kind : Kind schema .logOnly)
    (payload : kind.Payload) : Session schema :=
  let event : LoggedEvent schema := {
    visibility := .logOnly
    seq := session.nextSeq
    kind
    payload
    intent := .token
  }
  session.append event rfl session.surface
    (SurfaceTransition.logOnly session.nextSeq kind payload .token session.surface)
    session.valid.surface_nodup

/-- Append a model-visible event with unique references to earlier physical log entries. -/
def appendSurface
    {schema : ExtensionSchema}
    (session : Session schema)
    (kind : Kind schema .surface)
    (payload : kind.Payload)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session schema :=
  let event : LoggedEvent schema := {
    visibility := .surface
    seq := session.nextSeq
    kind
    payload
    intent := .append sourceEventSeqs
  }
  let node : SurfaceNode := {
    seq := session.nextSeq
    message := kind.surfaceMessage payload
  }
  have fresh : session.nextSeq ∉ session.surface.map SurfaceNode.seq := by
    intro member
    rcases List.mem_map.mp member with ⟨prior, priorMember, priorEq⟩
    exact (Nat.ne_of_lt (session.valid.surface_references_earlier prior priorMember)) priorEq
  session.append event rfl (session.surface ++ [node])
    (SurfaceTransition.append session.nextSeq kind payload sourceEventSeqs sourcesNodup
      sourcesEarlier session.surface)
    (by
      simp only [List.map_append, List.map_singleton]
      refine List.nodup_append.mpr ⟨session.valid.surface_nodup, by simp, ?_⟩
      intro existing existingMember added addedMember
      simp only [List.mem_singleton] at addedMember
      subst added
      intro equals
      subst existing
      exact fresh existingMember)

@[simp]
theorem protocolProjection_appendRequestHeader
    (session : Session noExtensions)
    (header : RequestHeader) :
    protocolProjection (session.appendLogOnly .requestHeader header).events =
      protocolProjection session.events := by
  simp [Session.appendLogOnly, Session.append, protocolProjection,
    LoggedEvent.protocolEvent?]

@[simp]
theorem protocolProjection_appendUserMessage
    (session : Session noExtensions)
    (content : String) :
    protocolProjection
        (session.appendSurface .userMessage { content } [] (by simp) (by simp)).events =
      protocolProjection session.events := by
  simp [Session.appendSurface, Session.append, protocolProjection,
    LoggedEvent.protocolEvent?]

@[simp]
theorem protocolProjection_appendAssistantMessage
    (session : Session noExtensions)
    (payload : AssistantMessagePayload) :
    protocolProjection
        (session.appendSurface .assistantMessage payload [] (by simp) (by simp)).events =
      protocolProjection session.events := by
  simp [Session.appendSurface, Session.append, protocolProjection,
    LoggedEvent.protocolEvent?]

/-- Model messages for a session are exactly its certified surface nodes. -/
def messages {schema : ExtensionSchema} (session : Session schema) : List Message :=
  deriveMessages session.surface

@[simp]
theorem messages_eq_surface {schema : ExtensionSchema} (session : Session schema) :
    session.messages = session.surface.map SurfaceNode.message := rfl

end Session

/-- A model request tied to the exact header, messages, and physical-log length of a session. -/
structure ModelRequest {schema : ExtensionSchema} (session : Session schema) where
  header : RequestHeader
  messages : List Message
  messages_eq : messages = session.messages
  latestHeader_eq : latestRequestHeader session.events = some header
  logLength : Nat
  logLength_eq : logLength = session.events.length
  nextSeq_eq : logLength = session.nextSeq

/-- Construct a request exactly when at least one request-header event has been logged. -/
def mkRequest {schema : ExtensionSchema} (session : Session schema) :
    Option (ModelRequest session) :=
  match header_eq : session.latestHeader with
  | none => none
  | some header =>
      some {
        header
        messages := session.messages
        messages_eq := rfl
        latestHeader_eq := by
          calc
            latestRequestHeader session.events = session.latestHeader :=
              session.valid.latest_header_eq
            _ = some header := header_eq
        logLength := session.events.length
        logLength_eq := rfl
        nextSeq_eq := session.valid.length_eq_nextSeq
      }

/-! ## Certified executable examples -/

def exampleHeader : RequestHeader where
  provider := "deepseek"
  model := "deepseek-chat"
  system := some "Use tools when useful."
  toolSchemas := [{
    name := "lookup"
    description := "Look up a key"
    inputSchema := "{\"type\":\"object\"}"
  }]

def exampleCall : ToolCall where
  id := ⟨7⟩
  name := "lookup"
  arguments := "{\"key\":\"answer\"}"

def headerEvent : LoggedEvent noExtensions where
  visibility := .logOnly
  seq := 0
  kind := .requestHeader
  payload := exampleHeader
  intent := .token

def userEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 1
  kind := .userMessage
  payload := { content := "What is the answer?" }
  intent := .append []

def assistantEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 2
  kind := .assistantMessage
  payload := {
    turn := 0
    step := 0
    content := "I will look it up."
    rawToolCalls := [exampleCall]
  }
  intent := .append [1]

def callEvent : LoggedEvent noExtensions where
  visibility := .logOnly
  seq := 3
  kind := .toolCall
  payload := { turn := 0, step := 0, call := exampleCall }
  intent := .token

def resultEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 4
  kind := .toolResult
  payload := {
    turn := 0
    step := 0
    callId := exampleCall.id
    content := "42"
    isError := false
  }
  intent := .append [3]

def userNode : SurfaceNode :=
  { seq := 1, message := .user "What is the answer?" }

def assistantNode : SurfaceNode :=
  { seq := 2, message := .assistant "I will look it up." [exampleCall] }

def resultNode : SurfaceNode :=
  { seq := 4, message := .toolResult exampleCall.id "42" false }

theorem headerLog : ValidLog noExtensions 1 [headerEvent] [] (some exampleHeader) := by
  simpa [headerEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc ValidLog.empty headerEvent rfl
      (SurfaceTransition.logOnly 0 (.requestHeader : Kind noExtensions .logOnly)
        exampleHeader .token []) (by simp))

theorem userLog : ValidLog noExtensions 2 [headerEvent, userEvent] [userNode]
    (some exampleHeader) := by
  have transition : SurfaceTransition userEvent [] [userNode] := by
    simpa [userEvent, userNode] using
      (SurfaceTransition.append 1 (.userMessage : Kind noExtensions .surface)
        { content := "What is the answer?" } [] (by simp) (by simp) [])
  simpa [userEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc headerLog userEvent rfl transition (by simp [userNode]))

theorem assistantLog :
    ValidLog noExtensions 3 [headerEvent, userEvent, assistantEvent]
      [userNode, assistantNode] (some exampleHeader) := by
  have transition : SurfaceTransition assistantEvent [userNode] [userNode, assistantNode] := by
    simpa [assistantEvent, assistantNode] using
      (SurfaceTransition.append 2 (.assistantMessage : Kind noExtensions .surface)
        {
          turn := 0
          step := 0
          content := "I will look it up."
          rawToolCalls := [exampleCall]
        }
        [1] (by simp) (by simp) [userNode])
  simpa [assistantEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc userLog assistantEvent rfl transition (by simp [userNode, assistantNode]))

theorem callLog :
    ValidLog noExtensions 4 [headerEvent, userEvent, assistantEvent, callEvent]
      [userNode, assistantNode] (some exampleHeader) := by
  have transition :
      SurfaceTransition callEvent [userNode, assistantNode] [userNode, assistantNode] :=
    SurfaceTransition.logOnly 3 (.toolCall : Kind noExtensions .logOnly)
      { turn := 0, step := 0, call := exampleCall } .token [userNode, assistantNode]
  simpa [callEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc assistantLog callEvent rfl transition (by simp [userNode, assistantNode]))

theorem certifiedLog :
    ValidLog noExtensions 5 [headerEvent, userEvent, assistantEvent, callEvent, resultEvent]
      [userNode, assistantNode, resultNode] (some exampleHeader) := by
  have transition : SurfaceTransition resultEvent [userNode, assistantNode]
      [userNode, assistantNode, resultNode] := by
    simpa [resultEvent, resultNode] using
      (SurfaceTransition.append 4 (.toolResult : Kind noExtensions .surface)
        {
          turn := 0
          step := 0
          callId := exampleCall.id
          content := "42"
          isError := false
        }
        [3] (by simp) (by simp) [userNode, assistantNode])
  simpa [resultEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc callLog resultEvent rfl transition
      (by simp [userNode, assistantNode, resultNode]))

/-- A complete header/user/assistant/tool-call/tool-result certified session. -/
def certifiedSession : Session noExtensions where
  nextSeq := 5
  events := [headerEvent, userEvent, assistantEvent, callEvent, resultEvent]
  surface := [userNode, assistantNode, resultNode]
  latestHeader := some exampleHeader
  valid := certifiedLog

/-- The rich example's tool slice is an intrinsic call/result protocol trace. -/
def certifiedToolTrace : Trace (.step 0 0 []) (.step 0 0 []) :=
  .cons (.toolCall exampleCall.id (by simp)) <|
  .cons (.toolResult exampleCall.id (by simp)) .nil

theorem certifiedSession_protocolProjection :
    protocolProjection certifiedSession.events = certifiedToolTrace.erase := rfl

def certifiedSessionProtocol :
    ProtocolCertificate certifiedSession (.step 0 0 []) (.step 0 0 []) where
  trace := certifiedToolTrace
  projection_eq := certifiedSession_protocolProjection

theorem certifiedSession_protocol_replays :
    replayRaw (.step 0 0 []) (protocolProjection certifiedSession.events) =
      .ok (.step 0 0 []) :=
  certifiedSessionProtocol.replays

theorem certifiedSession_messages :
    certifiedSession.messages =
      [.user "What is the answer?",
       .assistant "I will look it up." [exampleCall],
       .toolResult exampleCall.id "42" false] := rfl

theorem certifiedSession_request_exists : (mkRequest certifiedSession).isSome := by
  rfl

theorem emptySession_request_eq_none : mkRequest (Session.empty noExtensions) = none := rfl

theorem certifiedSession_request_values :
    match mkRequest certifiedSession with
    | none => False
    | some request =>
        request.header = exampleHeader ∧
        request.messages = certifiedSession.messages ∧
        request.logLength = 5 := by
  simp [mkRequest, certifiedSession]

def replacementEvent : LoggedEvent noExtensions where
  visibility := .surface
  seq := 5
  kind := .assistantMessage
  payload := { turn := 0, step := 0, content := "The answer is 42.", rawToolCalls := [] }
  intent := .replace 2 4 [2, 4]

def replacementNode : SurfaceNode :=
  { seq := 5, message := .assistant "The answer is 42." [] }

theorem replacementTransition :
    SurfaceTransition replacementEvent
      [userNode, assistantNode, resultNode]
      [userNode, replacementNode] := by
  simpa [replacementEvent, replacementNode] using
    (SurfaceTransition.replace 5 (.assistantMessage : Kind noExtensions .surface)
      { turn := 0, step := 0, content := "The answer is 42.", rawToolCalls := [] }
      2 4 [2, 4] [userNode] assistantNode [resultNode] [] rfl rfl
      (by simp) (by simp) (by
        intro node member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [assistantNode, resultNode]))

theorem replacementLog :
    ValidLog noExtensions 6
      [headerEvent, userEvent, assistantEvent, callEvent, resultEvent, replacementEvent]
      [userNode, replacementNode] (some exampleHeader) := by
  simpa [replacementEvent, LoggedEvent.updateHeader, Kind.projectHeader] using
    (ValidLog.snoc certifiedLog replacementEvent rfl replacementTransition (by
      simp [userNode, replacementNode]))

/-- A certified replacement shadows the assistant/tool-result interval with one summary node. -/
def replacementSession : Session noExtensions where
  nextSeq := 6
  events := [headerEvent, userEvent, assistantEvent, callEvent, resultEvent, replacementEvent]
  surface := [userNode, replacementNode]
  latestHeader := some exampleHeader
  valid := replacementLog

theorem replacementSession_messages :
    replacementSession.messages =
      [.user "What is the answer?", .assistant "The answer is 42." []] := rfl

theorem replacementSession_sources_cover_shadowed :
    ∀ node ∈ [assistantNode, resultNode], node.seq ∈ [2, 4] := by
  intro node member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [assistantNode, resultNode]

end Cordis.Session
