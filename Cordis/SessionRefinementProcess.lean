import Cordis.DeepSeekHarnessEventProcessPrefix
import Cordis.SessionRefinementTextCodec

/-!
# Process-backed canonical session-event JSONL

This module feeds the canonical `SessionRefinement.Codec` fixture through an actual local
subprocess.  The process adapter keeps the existing dependent cursor: every observed JSON object
retains its raw line, semantic `WireEvent`, decode proof, refined state transition, and final
session endpoint.  The subprocess itself is deliberately a test executable (`sh`), so this is
evidence for the local process/JSONL boundary rather than a claim about provider reachability,
credential validity, logger authenticity, scheduler behavior, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinementProcess

open Cordis
open Cordis.DeepSeekHarnessEventPrefix
open Cordis.DeepSeekHarnessEventProcessPrefix
open Cordis.SessionRefinement

/-- A process-safe canonical sequence whose physical indices start at the empty cursor. -/
def canonicalProcessEvents : List WireEvent := [
  { seq := { value := 0, safe := by decide }, time := { value := 100, safe := by decide },
    payload := .turnStart { value := 1, safe := by decide } },
  { seq := { value := 1, safe := by decide }, time := { value := 101, safe := by decide },
    payload := .stepStart { value := 1, safe := by decide } { value := 1, safe := by decide } },
  { seq := { value := 2, safe := by decide }, time := { value := 102, safe := by decide },
    payload := .assistantChunk SessionRefinement.Codec.mixedAssistantChunk },
  { seq := { value := 3, safe := by decide }, time := { value := 103, safe := by decide },
    payload := .stepEnd { value := 1, safe := by decide } { value := 1, safe := by decide } }
]

/-- The exact AST arguments emitted to the local process fixture. -/
def canonicalProcessJson : List Lean.Json :=
  canonicalProcessEvents.map fun event =>
    match SessionRefinement.Codec.encodeWireEvent event with
    | .ok json => json
    | .error _ => Lean.Json.null

/-- A configured process whose arguments are complete canonical JSONL event lines. -/
def canonicalProcess : EventProcessConfig where
  command := "sh"
  args :=
    #[
      "-c",
      "for line in \"$@\"; do printf '%s\\n' \"$line\"; done",
      "cordis-session-codec-fixture"
    ] ++ (canonicalProcessJson.map Lean.Json.compress).toArray

/-- The real local subprocess fixture, retaining every cursor certificate on success. -/
def runCanonicalProcess :
    IO (Except ProcessPrefixError (ProcessPrefixResult EntryPolicy.never)) :=
  execute EntryPolicy.never 32 canonicalProcess

namespace Example

def expectedTags : List String :=
  ["turn/start", "step/start", "assistant/chunk", "step/end"]

def tags (result : ProcessPrefixResult EntryPolicy.never) : List String :=
  result.cursor.entries.map fun entry =>
    match entry.wire.payload with
    | .turnStart _ => "turn/start"
    | .stepStart _ _ => "step/start"
    | .assistantChunk _ => "assistant/chunk"
    | .stepEnd _ _ => "step/end"
    | .toolCall _ _ _ _ _ => "tool/call"
    | _ => "other"

def summary (result : ProcessPrefixResult EntryPolicy.never) :
    Nat × Nat × Bool × List String :=
  (
    result.cursor.entries.length,
    result.cursor.final.session.nextSeq,
    result.stop.isCompleted,
    tags result
  )

def expectedSummary : Nat × Nat × Bool × List String :=
  (4, 4, true, expectedTags)

def summaryMatches (result : ProcessPrefixResult EntryPolicy.never) : Bool :=
  summary result = expectedSummary

end Example

theorem processResult_projection
    {result : ProcessPrefixResult EntryPolicy.never} :
    result.cursor.sequence.protocolTrace.erase = result.cursor.sequence.runtimeEvents := by
  exact PrefixSequence.protocolTrace_erase result.cursor.sequence

end Cordis.SessionRefinementProcess
