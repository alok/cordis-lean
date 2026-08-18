import Cordis.RichStream
import Cordis.Session

/-!
# Rich-stream to session bridge

DeepSeek providers identify tool calls with strings, while the local session protocol assigns
numeric `CallId`s. This module makes that seam explicit: a `CallIdAssignment` must provide one
unique numeric ID for every projected provider tool call before a rich assistant result can enter
the canonical session surface.

The bridge does not claim that a provider ID is globally authentic, parse tool arguments, or
persist either representation. It preserves visible text, tool order, names, and raw argument
strings after the rich stream validator has certified block assembly.
-/

namespace Cordis.StreamSession

open Cordis

/-- One unique numeric ID for every provider tool call in the projected assistant view. -/
structure CallIdAssignment (view : RichStream.AssistantMessageView) where
  ids : List CallId
  length_eq : ids.length = view.rawToolCalls.length
  nodup : ids.Nodup

/-- Pair provider calls with their certified local session IDs in model order. -/
def toSessionToolCalls
    (view : RichStream.AssistantMessageView)
    (assignment : CallIdAssignment view) : List Session.ToolCall :=
  List.zipWith (fun call id => {
    id
    name := call.name
    arguments := call.rawArguments
  }) view.rawToolCalls assignment.ids

/-- The bridge neither drops nor invents tool calls. -/
theorem toSessionToolCalls_length
    (view : RichStream.AssistantMessageView)
    (assignment : CallIdAssignment view) :
    (toSessionToolCalls view assignment).length = view.rawToolCalls.length := by
  simp [toSessionToolCalls, List.length_zipWith, assignment.length_eq]

/-- Convert a certified rich-stream view to the exact session assistant payload. -/
def toAssistantPayload
    (turn step : Nat)
    (view : RichStream.AssistantMessageView)
    (assignment : CallIdAssignment view) : Session.AssistantMessagePayload where
  turn
  step
  content := view.content
  rawToolCalls := toSessionToolCalls view assignment

/-- Append a validated rich assistant view to a proof-carrying session surface. -/
def appendAssistant
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (view : RichStream.AssistantMessageView)
    (assignment : CallIdAssignment view)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  session.appendSurface .assistantMessage
    (toAssistantPayload turn step view assignment) sourceEventSeqs sourcesNodup sourcesEarlier

/-! ## Certified bridge example -/

def interleavedView : RichStream.AssistantMessageView :=
  RichStream.toAssistantMessageView RichStream.interleavedBlocks

def interleavedAssignment : CallIdAssignment interleavedView where
  ids := [{ value := 40 }, { value := 41 }]
  length_eq := rfl
  nodup := by decide

def interleavedPayload : Session.AssistantMessagePayload :=
  toAssistantPayload 3 2 interleavedView interleavedAssignment

theorem interleavedPayload_exact :
    interleavedPayload = {
      turn := 3
      step := 2
      content := "Hello world"
      rawToolCalls := [
        { id := { value := 40 }, name := "lookup", arguments := "{\"q\":\"lean\"}" },
        { id := { value := 41 }, name := "sum", arguments := "{\"xs\":[1,2]}" }
      ]
    } := rfl

def bridgedSession : Session.Session Session.noExtensions :=
  appendAssistant (Session.Session.empty Session.noExtensions) 3 2 interleavedView
    interleavedAssignment [] (by simp) (by simp)

theorem bridgedSession_messages :
    bridgedSession.messages = [
      .assistant "Hello world" [
        { id := { value := 40 }, name := "lookup", arguments := "{\"q\":\"lean\"}" },
        { id := { value := 41 }, name := "sum", arguments := "{\"xs\":[1,2]}" }
      ]
    ] := rfl

theorem interleaved_assignment_is_unique : interleavedAssignment.ids.Nodup :=
  interleavedAssignment.nodup

end Cordis.StreamSession
