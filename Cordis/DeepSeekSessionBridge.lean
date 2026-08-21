import Cordis.RichStream
import Cordis.StreamSession

/-!
# Certified rich-stream to session bridge

`RichStream` deliberately stops at a proof-carrying terminal assistant view,
while `Session` assigns numeric call IDs and requires source-event evidence.
This module connects those two layers without pretending that provider string
IDs are globally authentic: a caller must still supply a unique
`StreamSession.CallIdAssignment`, source sequence facts, and the surrounding
turn/step coordinates.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSessionBridge

open Cordis
open Cordis.RichStream

inductive BridgeError where
  | notTerminal
deriving DecidableEq, Repr

structure FinishedAssistant {start : RichStream.State} {raw : List RichStream.RawChunk}
    (validated : RichStream.ValidatedTrace start raw) where
  blocks : List RichStream.ContentBlock
  terminal : ∃ usage reason replay,
    validated.finish = .terminal blocks usage reason replay

namespace FinishedAssistant

def view {start : RichStream.State} {raw : List RichStream.RawChunk}
    {validated : RichStream.ValidatedTrace start raw}
    (finished : FinishedAssistant validated) : RichStream.AssistantMessageView :=
  RichStream.toAssistantMessageView finished.blocks

theorem terminal_state {start : RichStream.State} {raw : List RichStream.RawChunk}
    {validated : RichStream.ValidatedTrace start raw}
    (finished : FinishedAssistant validated) :
    ∃ usage reason replay,
      validated.finish = .terminal finished.blocks usage reason replay :=
  finished.terminal

end FinishedAssistant

def finishAssistant {start : RichStream.State} {raw : List RichStream.RawChunk}
    (validated : RichStream.ValidatedTrace start raw) :
    Except BridgeError (FinishedAssistant validated) :=
  match h : validated.finish with
  | .active _ _ => .error .notTerminal
  | .terminal blocks _ _ _ => .ok {
      blocks
      terminal := by
        exact ⟨_, _, _, h⟩
    }

def appendFinishedAssistant
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    {start : RichStream.State} {raw : List RichStream.RawChunk}
    {validated : RichStream.ValidatedTrace start raw}
    (finished : FinishedAssistant validated)
    (assignment : StreamSession.CallIdAssignment finished.view)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  StreamSession.appendAssistant session turn step finished.view assignment
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendFinishedAssistant_messages
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    {start : RichStream.State} {raw : List RichStream.RawChunk}
    {validated : RichStream.ValidatedTrace start raw}
    (finished : FinishedAssistant validated)
    (assignment : StreamSession.CallIdAssignment finished.view)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendFinishedAssistant session turn step finished assignment sourceEventSeqs
      sourcesNodup sourcesEarlier).messages =
      session.messages ++ [.assistant finished.view.content
        (StreamSession.toSessionToolCalls finished.view assignment)] := by
  simp [appendFinishedAssistant, StreamSession.appendAssistant,
    StreamSession.toAssistantPayload, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface]

end Cordis.DeepSeekSessionBridge
