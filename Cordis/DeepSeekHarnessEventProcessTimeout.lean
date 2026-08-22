import Cordis.DeepSeekHarnessEventProcessPrefix
import Std.Async.Basic
import Std.Async.Timer

/-!
# Process-backed blocked-read timeout

This module adds a real deadline around each synchronous stdout-line read.  A Lean asynchronous
timer races the blocking read; if the timer wins it kills and waits for the child, and the typed
result retains the exact cursor prefix, observed lines, exit code, stderr, and timeout stop.  The
timer is per-read rather than a fairness scheduler, and this remains local process evidence: it
does not claim arbitrary descendant cleanup, provider or executable authenticity, crash durability,
backpressure, or equivalence to a deployed asynchronous Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventProcessTimeout

open Cordis
open Cordis.DeepSeekHarnessEventPrefix
open Cordis.DeepSeekHarnessEventProcessPrefix

inductive TimeoutPrefixStop (policy : EntryPolicy) where
  | completed
  | fuelExhausted
  | cancelled
      (entry : Nat)
      (reason : String)
      (decided : policy.decide entry = true)
  | timedOut (entry : Nat) (timeoutMs : UInt32)
deriving Repr

namespace TimeoutPrefixStop

def isCompleted {policy : EntryPolicy} : TimeoutPrefixStop policy → Bool
  | .completed => true
  | .fuelExhausted | .cancelled .. | .timedOut .. => false

def isFuelExhausted {policy : EntryPolicy} : TimeoutPrefixStop policy → Bool
  | .completed | .cancelled .. | .timedOut .. => false
  | .fuelExhausted => true

def isCancelled {policy : EntryPolicy} : TimeoutPrefixStop policy → Bool
  | .completed | .fuelExhausted | .timedOut .. => false
  | .cancelled .. => true

def isTimedOut {policy : EntryPolicy} : TimeoutPrefixStop policy → Bool
  | .completed | .fuelExhausted | .cancelled .. => false
  | .timedOut .. => true

end TimeoutPrefixStop

structure TimedProcessPrefixResult (policy : EntryPolicy) where
  cursor : Cursor
  lines : List String
  consumed : Nat
  consumed_eq_entries : cursor.entries.length = consumed
  stop : TimeoutPrefixStop policy
  stop_consumed : match stop with
    | .cancelled entry _ _ => entry = consumed
    | .timedOut entry _ => entry = consumed
    | .completed | .fuelExhausted => True
  exitCode : Option UInt32
  stderr : String

namespace TimedProcessPrefixResult

def entries {policy : EntryPolicy} (result : TimedProcessPrefixResult policy) : Nat :=
  result.cursor.entries.length

theorem entries_eq_consumed {policy : EntryPolicy}
    (result : TimedProcessPrefixResult policy) :
    result.entries = result.consumed :=
  result.consumed_eq_entries

theorem timeout_entry_eq_consumed {policy : EntryPolicy}
    (result : TimedProcessPrefixResult policy)
    {entry : Nat} {timeoutMs : UInt32}
    (stop_eq : result.stop = .timedOut entry timeoutMs) :
    entry = result.consumed := by
  simpa [stop_eq] using result.stop_consumed

end TimedProcessPrefixResult

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

private inductive TimedLine where
  | line (line : String)
  | timedOut
  | io (message : String)
deriving Inhabited

private def readLineWithTimeout
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stdout : IO.FS.Stream)
    (timeoutMs : UInt32) : IO TimedLine := do
  let sleeper ← Std.Async.Async.block <|
    Std.Async.Sleep.mk (Std.Time.Millisecond.Offset.ofNat timeoutMs.toNat)
  let readTask ← IO.asTask stdout.getLine
  let readAction : Std.Async.Async TimedLine := do
    try
      let line ← Std.Async.Async.ofAsyncTask readTask
      pure (.line line)
    catch error =>
      pure (.io (toString error))
  let timeoutAction : Std.Async.Async TimedLine := do
    sleeper.wait
    try
      child.kill
    catch _ =>
      pure ()
    pure .timedOut
  try
    let result ← Std.Async.Async.block (Std.Async.Async.race readAction timeoutAction)
    if result matches .line _ then
      sleeper.stop
    if result matches .timedOut then
      try
        discard <| IO.wait readTask
      catch _ =>
        pure ()
    pure result
  catch error =>
    pure (.io (toString error))

private def loop
    (policy : EntryPolicy)
    (fuel : Nat)
    (timeoutMs : UInt32)
    {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg)
    (stderrTask : Task (Except IO.Error String))
    (stdout : IO.FS.Stream)
    (cursor : Cursor)
    (linesRev : List String)
    (consumed : Nat)
    (consumed_eq_entries : cursor.entries.length = consumed) :
    IO (Except ProcessPrefixError (TimedProcessPrefixResult policy)) := do
  match fuel with
  | 0 =>
      cleanup child stderrTask
      pure <| .ok {
        cursor
        lines := linesRev.reverse
        consumed
        consumed_eq_entries
        stop := .fuelExhausted
        stop_consumed := trivial
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
          stop_consumed := rfl
          exitCode := none
          stderr := ""
        }
      else
        try
          match ← readLineWithTimeout child stdout timeoutMs with
          | .timedOut =>
              let exitCode ← child.wait
              let stderr ← IO.ofExcept stderrTask.get
              pure <| .ok {
                cursor
                lines := linesRev.reverse
                consumed
                consumed_eq_entries
                stop := .timedOut consumed timeoutMs
                stop_consumed := rfl
                exitCode := some exitCode
                stderr
              }
          | .io message =>
              cleanup child stderrTask
              pure (.error (.io message))
          | .line line =>
              if line.isEmpty then
                let exitCode ← child.wait
                let stderr ← IO.ofExcept stderrTask.get
                if exitCode == 0 then
                  pure <| .ok {
                    cursor
                    lines := linesRev.reverse
                    consumed
                    consumed_eq_entries
                    stop := .completed
                    stop_consumed := trivial
                    exitCode := some exitCode
                    stderr
                  }
                else
                  pure (.error (.exited exitCode stderr))
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
                        loop policy fuel timeoutMs child stderrTask stdout next
                          (line :: linesRev) (consumed + 1) next_eq_entries
        catch error =>
          cleanup child stderrTask
          pure (.error (.io (toString error)))

def executeWithTimeout
    (policy : EntryPolicy)
    (maxReads : Nat)
    (timeoutMs : UInt32)
    (config : EventProcessConfig) :
    IO (Except ProcessPrefixError (TimedProcessPrefixResult policy)) := do
  try
    let child ← IO.Process.spawn {
      cmd := config.command
      args := config.args
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    loop policy maxReads timeoutMs child stderrTask (IO.FS.Stream.ofHandle child.stdout)
      Cursor.initial [] 0 (by rfl)
  catch error =>
    pure (.error (.spawn (toString error)))

def blockedReadProcess : EventProcessConfig where
  command := "sh"
  args := #["-c", "exec sleep 2", "cordis-event-prefix-timeout"]

def blockedReadProcessRun :
    IO (Except ProcessPrefixError (TimedProcessPrefixResult EntryPolicy.never)) :=
  executeWithTimeout EntryPolicy.never 32 100 blockedReadProcess

def delayedToolProcess : EventProcessConfig where
  command := "sh"
  args := #[
    "-c",
    "printf '%s\\n' \"$1\"; printf 'timeout-stderr\\n' >&2; exec sleep 2",
    "cordis-event-prefix-timeout-tool",
    (SessionRefinement.toolMessageExampleJson.head?.map Lean.Json.compress).getD "null"
  ]

def delayedToolProcessRun :
    IO (Except ProcessPrefixError (TimedProcessPrefixResult EntryPolicy.never)) :=
  executeWithTimeout EntryPolicy.never 32 100 delayedToolProcess

def fastProcessRun :
    IO (Except ProcessPrefixError (TimedProcessPrefixResult EntryPolicy.never)) :=
  executeWithTimeout EntryPolicy.never 32 2000 toolEventProcess

theorem processResult_endpoint_sequence {policy : EntryPolicy}
    (result : TimedProcessPrefixResult policy) :
    result.cursor.sequence.protocolTrace.erase =
      result.cursor.sequence.runtimeEvents := by
  exact PrefixSequence.protocolTrace_erase result.cursor.sequence

end Cordis.DeepSeekHarnessEventProcessTimeout
