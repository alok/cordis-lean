import Cordis.DeepSeekHarnessEventPrefix

/-!
# Process-backed incremental current-Harness event prefix

`DeepSeekHarnessEventPrefix` supplies the pure dependent cursor.  This module feeds that cursor
from one complete stdout line at a time using an explicitly configured local process.  The result
retains the exact lines observed, the cursor endpoint, the consumed count, and the typed stop.

The boundary is deliberately line-oriented: it does not claim byte framing, blocked-read
interruption, backpressure, provider or executable authenticity, crash durability, or equivalence
to a deployed DeepSeek Harness.  A fuel or policy stop kills and waits for the child before
returning, so the local cleanup action is observable without being promoted to a global guarantee.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventProcessPrefix

open Cordis
open Cordis.DeepSeekHarnessEventPrefix

structure EventProcessConfig where
  command : String
  args : Array String

inductive ProcessPrefixError where
  | spawn (message : String)
  | line (line : Nat) (message : String)
  | event (line : Nat) (error : PrefixError)
  | exited (code : UInt32) (stderr : String)
  | io (message : String)
deriving Repr

structure ProcessPrefixResult (policy : EntryPolicy) where
  cursor : Cursor
  lines : List String
  consumed : Nat
  consumed_eq_entries : cursor.entries.length = consumed
  stop : PrefixStop policy
  exitCode : Option UInt32
  stderr : String

namespace ProcessPrefixResult

def entries {policy : EntryPolicy} (result : ProcessPrefixResult policy) : Nat :=
  result.cursor.entries.length

def isCompleted {policy : EntryPolicy} (result : ProcessPrefixResult policy) : Bool :=
  result.stop.isCompleted

def isFuelExhausted {policy : EntryPolicy} (result : ProcessPrefixResult policy) : Bool :=
  result.stop.isFuelExhausted

def isCancelled {policy : EntryPolicy} (result : ProcessPrefixResult policy) : Bool :=
  result.stop.isCancelled

theorem entries_eq_consumed {policy : EntryPolicy} (result : ProcessPrefixResult policy) :
    result.entries = result.consumed :=
  result.consumed_eq_entries

end ProcessPrefixResult

theorem Cursor.push_entries_eq {cursor : Cursor} {raw : Lean.Json} {next : Cursor}
    (pushed : Cursor.push cursor raw = .ok next) :
    next.entries.length = cursor.entries.length + 1 := by
  unfold Cursor.push at pushed
  split at pushed <;> try contradiction
  split at pushed <;> try contradiction
  cases pushed
  simp [Cursor.pushDecoded]

private def stripLineEnding (line : String) : String :=
  if line.endsWith "\n" then (line.dropEnd 1).toString else line

private def cleanup
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String)) : IO Unit := do
  try
    child.kill
  catch _ =>
    pure ()
  try
    discard <| child.wait
  catch _ =>
    pure ()
  try
    discard <| IO.ofExcept stderrTask.get
  catch _ =>
    pure ()

private def finish
    (policy : EntryPolicy)
    (cursor : Cursor)
    (linesRev : List String)
    (consumed : Nat)
    (consumed_eq_entries : cursor.entries.length = consumed)
    (stderr : String)
    (exitCode : UInt32) : Except ProcessPrefixError (ProcessPrefixResult policy) :=
  if exitCode == 0 then
    .ok {
      cursor
      lines := linesRev.reverse
      consumed
      consumed_eq_entries
      stop := .completed
      exitCode := some exitCode
      stderr
    }
  else
    .error (.exited exitCode stderr)

private def loop
    (policy : EntryPolicy)
    (fuel : Nat)
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String))
    (stdout : IO.FS.Stream)
    (cursor : Cursor)
    (linesRev : List String)
    (consumed : Nat)
    (consumed_eq_entries : cursor.entries.length = consumed) :
    IO (Except ProcessPrefixError (ProcessPrefixResult policy)) := do
  match fuel with
  | 0 =>
      cleanup child stderrTask
      pure <| .ok {
        cursor
        lines := linesRev.reverse
        consumed
        consumed_eq_entries
        stop := .fuelExhausted
        exitCode := none
        stderr := ""
      }
  | fuel + 1 =>
      if decided : policy.decide consumed then
        cleanup child stderrTask
        pure <| .ok {
          cursor
          lines := linesRev.reverse
          consumed
          consumed_eq_entries
          stop := .cancelled consumed (policy.reason consumed) decided
          exitCode := none
          stderr := ""
        }
      else
        try
          let line ← stdout.getLine
          if line.isEmpty then
            let exitCode ← child.wait
            let stderr ← IO.ofExcept stderrTask.get
            pure <| finish policy cursor linesRev consumed consumed_eq_entries stderr exitCode
          else
            let line := stripLineEnding line
            match Lean.Json.parse line.trimAscii.toString with
            | .error message =>
                cleanup child stderrTask
                pure (.error (.line consumed message))
            | .ok raw =>
                match pushed : Cursor.push cursor raw with
                | .error error =>
                    cleanup child stderrTask
                    pure (.error (.event consumed error))
                | .ok next =>
                    have next_eq_entries : next.entries.length = consumed + 1 := by
                      calc
                        next.entries.length = cursor.entries.length + 1 :=
                          Cursor.push_entries_eq pushed
                        _ = consumed + 1 := by rw [consumed_eq_entries]
                    loop policy fuel child stderrTask stdout next (line :: linesRev)
                      (consumed + 1) next_eq_entries
        catch error =>
          cleanup child stderrTask
          pure (.error (.io (toString error)))

/-- Read complete JSON objects from a configured process into the dependent cursor. -/
def execute
    (policy : EntryPolicy)
    (maxReads : Nat)
    (config : EventProcessConfig) :
    IO (Except ProcessPrefixError (ProcessPrefixResult policy)) := do
  try
    let child ← IO.Process.spawn {
      cmd := config.command
      args := config.args
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    loop policy maxReads child stderrTask (IO.FS.Stream.ofHandle child.stdout)
      Cursor.initial [] 0 (by rfl)
  catch error =>
    pure (.error (.spawn (toString error)))

def toolEventProcessArgs : Array String :=
  #[
    "-c",
    "for line in \"$@\"; do printf '%s\\n' \"$line\"; done",
    "cordis-event-prefix-fixture"
  ] ++ (SessionRefinement.toolMessageExampleJson.map Lean.Json.compress).toArray

def toolEventProcess : EventProcessConfig where
  command := "sh"
  args := toolEventProcessArgs

def toolProcessRun :
    IO (Except ProcessPrefixError (ProcessPrefixResult EntryPolicy.never)) :=
  execute EntryPolicy.never 32 toolEventProcess

def fuelProcessRun :
    IO (Except ProcessPrefixError (ProcessPrefixResult EntryPolicy.never)) :=
  execute EntryPolicy.never 2 toolEventProcess

def cancellationProcess : EventProcessConfig where
  command := "sh"
  args := #[
    "-c",
    "printf '%s\\n' \"$1\"; sleep 1",
    "cordis-event-prefix-cancellation",
    (SessionRefinement.toolMessageExampleJson.head?.map Lean.Json.compress).getD "null"
  ]

def cancellationProcessRun :
    IO (Except ProcessPrefixError
      (ProcessPrefixResult (EntryPolicy.atEntry 0 "process-prefix-cancelled"))) :=
  execute (EntryPolicy.atEntry 0 "process-prefix-cancelled") 32 cancellationProcess

def malformedProcess : EventProcessConfig where
  command := "sh"
  args := #["-c", "printf '%s\\n' '{not-json}'", "cordis-event-prefix-malformed"]

def malformedProcessRun :
    IO (Except ProcessPrefixError (ProcessPrefixResult EntryPolicy.never)) :=
  execute EntryPolicy.never 32 malformedProcess

def nonzeroProcess : EventProcessConfig where
  command := "sh"
  args := #["-c", "printf '%s\\n' 'fixture-stderr' >&2; exit 7", "cordis-event-prefix-nonzero"]

def nonzeroProcessRun :
    IO (Except ProcessPrefixError (ProcessPrefixResult EntryPolicy.never)) :=
  execute EntryPolicy.never 32 nonzeroProcess

theorem processResult_endpoint_sequence {policy : EntryPolicy}
    (result : ProcessPrefixResult policy) :
    result.cursor.sequence.protocolTrace.erase =
      result.cursor.sequence.runtimeEvents := by
  exact PrefixSequence.protocolTrace_erase result.cursor.sequence

end Cordis.DeepSeekHarnessEventProcessPrefix
