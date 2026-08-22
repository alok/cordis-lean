import Cordis.DeepSeekHarnessSchemaLift
import Cordis.SessionExtensionRefinement
import Cordis.SessionRefinement

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessMixedReplay

open Cordis
open Cordis.SessionRefinement
open Cordis.SessionExtensionRefinement
open Cordis.DeepSeekHarnessSchemaLift

universe u

inductive Row (schema : Session.ExtensionSchema) where
  | core (raw : Lean.Json)
  | extension (raw : Lean.Json)

structure MixedState (schema : Session.ExtensionSchema) where
  core : SessionRefinement.State
  session : Session.Session schema
  clock_eq : core.session.nextSeq = session.nextSeq
  surface_eq : core.session.surface = session.surface
  header_eq : core.session.latestHeader = session.latestHeader
  protocol_eq : Session.protocolProjection session.events =
    Session.protocolProjection core.session.events

def MixedState.initial (schema : Session.ExtensionSchema) : MixedState schema where
  core := SessionRefinement.State.initial
  session := Session.Session.empty schema
  clock_eq := rfl
  surface_eq := rfl
  header_eq := rfl
  protocol_eq := rfl

def liftCoreAppend
    {schema : Session.ExtensionSchema}
    {before : MixedState schema}
    {wire : SessionRefinement.WireEvent}
    (head : SessionRefinement.RefinedEvent before.core wire) :
    Session.ValidatedAppend before.session
      (liftEvent (schema := schema) head.candidate.localEvent) := by
  let sourceAppend := head.append
  exact {
    nextSurface := sourceAppend.nextSurface
    seq_eq := by
      rw [liftEvent_seq, sourceAppend.seq_eq, before.clock_eq]
    transition := by
      rw [← before.surface_eq]
      exact liftTransition sourceAppend.transition
    surfaceNodup := by
      exact sourceAppend.surfaceNodup
  }

def coreAfter
    {schema : Session.ExtensionSchema}
    {before : MixedState schema}
    {wire : SessionRefinement.WireEvent}
    (head : SessionRefinement.RefinedEvent before.core wire) : MixedState schema where
  core := head.after
  session := (liftCoreAppend head).apply
  clock_eq := by
    change head.after.session.nextSeq = (liftCoreAppend head).apply.nextSeq
    simp only [SessionRefinement.RefinedEvent.after, Session.ValidatedAppend.apply,
      Session.Session.append]
    rw [before.clock_eq]
  surface_eq := by
    change head.after.session.surface = (liftCoreAppend head).apply.surface
    rfl
  header_eq := by
    change head.candidate.localEvent.updateHeader before.core.session.latestHeader =
      (liftEvent (schema := schema) head.candidate.localEvent).updateHeader
        before.session.latestHeader
    rw [liftEvent_updateHeader, before.header_eq]
  protocol_eq := by
    rw [Session.ValidatedAppend.apply_events, SessionRefinement.RefinedEvent.events_eq]
    simp only [Session.protocolProjection, List.filterMap_append]
    have hPrefix :
        List.filterMap Session.LoggedEvent.protocolEvent? before.session.events =
          List.filterMap Session.LoggedEvent.protocolEvent? before.core.session.events :=
      before.protocol_eq
    rw [hPrefix]
    simp only [List.filterMap]
    rw [liftEvent_protocol, head.projection_exact]

def extensionAfter
    {schema : Session.ExtensionSchema}
    {before : MixedState schema}
    (event : SessionExtensionRefinement.ExtensionEvent schema)
    (kind : schema.Kind .logOnly)
    (payload : schema.Payload kind)
    (extension_eq : event.extension = .logOnly (.custom kind) payload)
    (seq_eq : event.seq.value = before.session.nextSeq) : MixedState schema where
  core := {
    before.core with
    session := before.core.session.appendLogOnly .sessionEndSeed {}
  }
  session := SessionExtensionRefinement.appendDecoded before.session event seq_eq
  clock_eq := by
    cases event with
    | mk seq time extension =>
        cases extension with
        | logOnly kind payload =>
            cases extension_eq
            simp [SessionExtensionRefinement.appendDecoded, Session.Session.appendLogOnly,
              Session.Session.append, before.clock_eq]
        | surface kind payload => cases extension_eq
  surface_eq := by
    cases event with
    | mk seq time extension =>
        cases extension with
        | logOnly kind payload =>
            cases extension_eq
            simp [SessionExtensionRefinement.appendDecoded, Session.Session.appendLogOnly,
              Session.Session.append, before.surface_eq]
        | surface kind payload => cases extension_eq
  header_eq := by
    cases event with
    | mk seq time extension =>
        cases extension with
        | logOnly kind payload =>
            cases extension_eq
            simp [SessionExtensionRefinement.appendDecoded, Session.Session.appendLogOnly,
              Session.Session.append, Session.LoggedEvent.updateHeader,
              Session.Kind.projectHeader, before.header_eq]
        | surface kind payload => cases extension_eq
  protocol_eq := by
    cases event with
    | mk seq time extension =>
        cases extension with
        | logOnly loggedKind loggedPayload =>
            cases loggedKind with
            | turnStart => cases extension_eq
            | turnEnd => cases extension_eq
            | stepStart => cases extension_eq
            | stepEnd => cases extension_eq
            | requestHeader => cases extension_eq
            | todoWrite => cases extension_eq
            | requestContext => cases extension_eq
            | sessionEndSeed => cases extension_eq
            | assistantChunk => cases extension_eq
            | assistantReasoning => cases extension_eq
            | toolCall => cases extension_eq
            | custom customKind =>
                cases extension_eq
                change Session.protocolProjection
                    (Session.Session.appendLogOnly before.session (.custom kind) payload).events =
                  Session.protocolProjection
                    (before.core.session.appendLogOnly .sessionEndSeed {}).events
                simp only [Session.Session.appendLogOnly, Session.Session.append,
                  Session.protocolProjection, List.filterMap_append]
                have hPrefix :
                    List.filterMap Session.LoggedEvent.protocolEvent? before.session.events =
                      List.filterMap Session.LoggedEvent.protocolEvent?
                        before.core.session.events :=
                  before.protocol_eq
                rw [hPrefix]
                rfl
        | surface kind payload => cases extension_eq

structure CoreStep
    {schema : Session.ExtensionSchema}
    (before : MixedState schema)
    (raw : Lean.Json) where
  wire : SessionRefinement.WireEvent
  decoded : SessionRefinement.decodeEvent raw = .ok wire
  refined : SessionRefinement.RefinedEvent before.core wire

def CoreStep.after
    {schema : Session.ExtensionSchema}
    {before : MixedState schema}
    {raw : Lean.Json}
    (step : CoreStep before raw) : MixedState schema :=
  coreAfter step.refined

structure ExtensionStep
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema)
    (before : MixedState schema)
    (raw : Lean.Json) where
  event : SessionExtensionRefinement.ExtensionEvent schema
  decoded : SessionExtensionRefinement.decodeEvent codec raw = .ok event
  kind : schema.Kind .logOnly
  payload : schema.Payload kind
  extension_eq : event.extension = .logOnly (.custom kind) payload
  seq_eq : event.seq.value = before.session.nextSeq

def ExtensionStep.after
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {before : MixedState schema}
    {raw : Lean.Json}
    (step : ExtensionStep codec before raw) : MixedState schema :=
  extensionAfter step.event step.kind step.payload step.extension_eq step.seq_eq

inductive MixedError where
  | coreDecode (error : SessionRefinement.DecodeError)
  | coreRefinement (error : SessionRefinement.RefinementError)
  | extensionDecode (error : SessionExtensionRefinement.ExtensionDecodeError)
  | extensionCoreKind
  | extensionSurfaceKind
  | extensionSequenceMismatch (expected actual : Nat)
  deriving DecidableEq, Repr

inductive MixedReplay
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema) :
    MixedState schema → List (Row schema) → MixedState schema → Type where
  | nil (state : MixedState schema) :
      MixedReplay codec state [] state
  | coreCons
      {before : MixedState schema}
      {raw : Lean.Json}
      {rest : List (Row schema)}
      {final : MixedState schema}
      (head : CoreStep before raw)
      (tail : MixedReplay codec head.after rest final) :
      MixedReplay codec before (.core raw :: rest) final
  | extensionCons
      {before : MixedState schema}
      {raw : Lean.Json}
      {rest : List (Row schema)}
      {final : MixedState schema}
      (head : ExtensionStep codec before raw)
      (tail : MixedReplay codec head.after rest final) :
      MixedReplay codec before (.extension raw :: rest) final

private def validateAt
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema)
    (before : MixedState schema) :
    (rows : List (Row schema)) →
      Except MixedError (Σ final : MixedState schema, MixedReplay codec before rows final)
  | [] => .ok ⟨before, .nil before⟩
  | Row.core raw :: rest =>
      match decoded : SessionRefinement.decodeEvent raw with
      | .error error => .error (.coreDecode error)
      | .ok wire =>
          match _refined : SessionRefinement.refineEvent before.core wire with
          | .error error => .error (.coreRefinement error)
          | .ok event =>
              let head : CoreStep before raw := { wire, decoded, refined := event }
              match _tailResult : validateAt codec head.after rest with
              | .error error => .error error
              | .ok ⟨final, tail⟩ => .ok ⟨final, .coreCons head tail⟩
  | Row.extension raw :: rest =>
      match decoded : SessionExtensionRefinement.decodeEvent codec raw with
      | .error error => .error (.extensionDecode error)
      | .ok event =>
          match event with
          | ⟨seq, time, extension⟩ =>
              match extension with
              | .surface _kind _payload => .error .extensionSurfaceKind
              | .logOnly kind payload =>
                  match kind with
                  | .custom customKind =>
                      if sequence : seq.value = before.session.nextSeq then
                        let head : ExtensionStep codec before raw := {
                          event := { seq, time, extension := .logOnly (.custom customKind) payload }

                          decoded := decoded
                          kind := customKind
                          payload
                          extension_eq := rfl
                          seq_eq := sequence
                        }
                        match _tailResult : validateAt codec head.after rest with
                        | .error error => .error error
                        | .ok ⟨final, tail⟩ => .ok ⟨final, .extensionCons head tail⟩
                      else
                        .error (.extensionSequenceMismatch before.session.nextSeq seq.value)
                  | .turnStart => .error .extensionCoreKind
                  | .turnEnd => .error .extensionCoreKind
                  | .stepStart => .error .extensionCoreKind
                  | .stepEnd => .error .extensionCoreKind
                  | .requestHeader => .error .extensionCoreKind
                  | .todoWrite => .error .extensionCoreKind
                  | .requestContext => .error .extensionCoreKind
                  | .sessionEndSeed => .error .extensionCoreKind
                  | .assistantChunk => .error .extensionCoreKind
                  | .assistantReasoning => .error .extensionCoreKind
                  | .toolCall => .error .extensionCoreKind

def validate
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema)
    (rows : List (Row schema)) :
    Except MixedError (Σ final : MixedState schema,
      MixedReplay codec (MixedState.initial schema) rows final) :=
  validateAt codec (MixedState.initial schema) rows

theorem coreAfter_nextSeq
    {schema : Session.ExtensionSchema}
    {before : MixedState schema}
    {raw : Lean.Json}
    (step : CoreStep before raw) :
    step.after.session.nextSeq = before.session.nextSeq + 1 := by
  change (liftCoreAppend step.refined).apply.nextSeq = before.session.nextSeq + 1
  simp [Session.ValidatedAppend.apply, Session.Session.append]

theorem extensionAfter_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {before : MixedState schema}
    {raw : Lean.Json}
    (step : ExtensionStep codec before raw) :
    step.after.session.nextSeq = before.session.nextSeq + 1 := by
  cases step with
  | mk event decoded kind payload extension_eq seq_eq =>
      cases event with
      | mk seq time extension =>
          cases extension with
          | surface loggedKind loggedPayload => cases extension_eq
          | logOnly loggedKind loggedPayload =>
              cases loggedKind with
              | turnStart => cases extension_eq
              | turnEnd => cases extension_eq
              | stepStart => cases extension_eq
              | stepEnd => cases extension_eq
              | requestHeader => cases extension_eq
              | todoWrite => cases extension_eq
              | requestContext => cases extension_eq
              | sessionEndSeed => cases extension_eq
              | assistantChunk => cases extension_eq
              | assistantReasoning => cases extension_eq
              | toolCall => cases extension_eq
              | custom customKind =>
                  cases extension_eq
                  simp [ExtensionStep.after, extensionAfter,
                    SessionExtensionRefinement.appendDecoded,
                    Session.Session.appendLogOnly, Session.Session.append]

namespace MixedReplay

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {before final : MixedState schema}
    {rows : List (Row schema)}
    (replay : MixedReplay codec before rows final) :
    final.session.nextSeq = before.session.nextSeq + rows.length := by
  induction replay with
  | nil state => simp
  | coreCons head tail ih =>
      rw [ih, coreAfter_nextSeq]
      simp only [List.length_cons]
      omega
  | extensionCons head tail ih =>
      rw [ih, extensionAfter_nextSeq]
      simp only [List.length_cons]
      omega

theorem final_projection_eq
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {before final : MixedState schema}
    {rows : List (Row schema)}
    (_replay : MixedReplay codec before rows final) :
    Session.protocolProjection final.session.events =
      Session.protocolProjection final.core.session.events :=
  final.protocol_eq

end MixedReplay

structure ValidatedMixedLog
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema)
    (rows : List (Row schema)) where
  final : MixedState schema
  replay : MixedReplay codec (MixedState.initial schema) rows final

def validateLog
    {schema : Session.ExtensionSchema}
    (codec : SessionExtensionRefinement.ExtensionCodec schema)
    (rows : List (Row schema)) :
    Except MixedError (ValidatedMixedLog codec rows) :=
  match _result : validate codec rows with
  | .error error => .error error
  | .ok ⟨final, replay⟩ => .ok { final, replay }

namespace ValidatedMixedLog

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {rows : List (Row schema)}
    (log : ValidatedMixedLog codec rows) :
    log.final.session.nextSeq = rows.length := by
  simpa [MixedState.initial, Session.Session.empty] using (log.replay.final_nextSeq)

theorem protocol_projection_eq
    {schema : Session.ExtensionSchema}
    {codec : SessionExtensionRefinement.ExtensionCodec schema}
    {rows : List (Row schema)}
    (log : ValidatedMixedLog codec rows) :
    Session.protocolProjection log.final.session.events =
      Session.protocolProjection log.final.core.session.events :=
  log.replay.final_projection_eq

end ValidatedMixedLog

namespace Example

open Cordis.DeepSeekHarnessExtensions
open Cordis.SessionExtensionRefinement.Example

def globalHeartbeatJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 1)),
  ("time", .num (Lean.JsonNumber.fromNat 200)),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

def coreTurnStartJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "turn/start"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("data", Lean.Json.mkObj [("turn", .num (Lean.JsonNumber.fromNat 1))])
]

def coreStepStartJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "step/start"),
  ("seq", .num (Lean.JsonNumber.fromNat 2)),
  ("time", .num (Lean.JsonNumber.fromNat 101)),
  ("data", Lean.Json.mkObj [
    ("turn", .num (Lean.JsonNumber.fromNat 1)),
    ("step", .num (Lean.JsonNumber.fromNat 1))])
]

def rows : List (Row exampleSchema) := [
  .core coreTurnStartJson,
  .extension globalHeartbeatJson,
  .core coreStepStartJson
]

def certificate : Except MixedError (ValidatedMixedLog exampleCodec rows) :=
  validateLog exampleCodec rows

theorem summary :
    (match certificate with
    | .error _ => none
    | .ok log =>
        some (log.final.session.nextSeq, log.final.session.events.length,
          log.final.session.surface.length)) =
      some (3, 3, 0) := by
  rfl

theorem protocol_exact :
    (match certificate with
    | .error _ => []
    | .ok log => Session.protocolProjection log.final.session.events) =
      [.turnStart 1, .stepStart 1 0] := by
  rfl

theorem projection_matches_core :
    (match certificate with
    | .error _ => True
    | .ok log =>
        Session.protocolProjection log.final.session.events =
          Session.protocolProjection log.final.core.session.events) := by
  rfl

def surfaceRow : Lean.Json := SessionExtensionRefinement.Example.bannerAfterHeartbeatJson

def surfaceRejected :
    Except MixedError (ValidatedMixedLog exampleCodec [.extension surfaceRow]) :=
  validateLog exampleCodec [.extension surfaceRow]

theorem surface_rejected :
    surfaceRejected = .error .extensionSurfaceKind := by
  rfl

def staleHeartbeat : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 99)),
  ("time", .num (Lean.JsonNumber.fromNat 201)),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

theorem stale_rejected :
    validateLog exampleCodec [.extension staleHeartbeat] =
      .error (.extensionSequenceMismatch 0 99) := by
  rfl

end Example

end Cordis.DeepSeekHarnessMixedReplay
