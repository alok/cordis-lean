import Cordis.Examples.DependentChoice
import Cordis.GenericSessionHarness
import Lean.Data.Json.Printer

/-!
# Rich-session instantiation for the dependent-choice catalog

This is the second rich-session configuration for the generic harness bridge. It deliberately
uses the dependent `Bool → (String | Nat)` tool rather than the counter catalog, and retains both
the successful revision call and the policy-rejected label call in one proof-carrying session.
-/

namespace Cordis.Examples.DependentChoiceSession

open Cordis
open Cordis.Examples.DependentChoice
open Cordis.GenericSessionHarness

def requestHeader : Session.RequestHeader where
  provider := "cordis-lean"
  model := "dependent-choice"
  system := some "Use the dependent workspace tool only through certified calls."
  toolSchemas := [{
    name := choiceSpec.name
    description := choiceSpec.description
    inputSchema := (wire.inputCodec .choose).schema.compress
  }]

def sessionConfig : SessionConfig Workspace Capability where
  core := config
  requestHeader := requestHeader
  userPrompt := "Inspect the current workspace."
  assistantPrompt := "Dispatching the dependent workspace call."

def run : Except RunnerError (RunnerState sessionConfig) :=
  RunnerState.runScript sessionConfig initialWorkspace [[rawRevision, rawLabel]]

def runState : Option (RunnerState sessionConfig) :=
  match run with
  | .ok state => some state
  | .error _ => none

def runSucceeded : Bool :=
  match run with
  | .ok _ => true
  | .error _ => false

def requestPresent : Bool :=
  match run with
  | .ok state => state.modelRequest.isSome
  | .error _ => false

def retainedRecordCount : Nat :=
  match run with
  | .ok state => state.records.length
  | .error _ => 0

theorem run_succeeds : runSucceeded = true := by
  rfl

theorem request_is_present : requestPresent = true := by
  rfl

theorem projection_replays (state : RunnerState sessionConfig) :
    Session.protocolProjection state.session.events = state.log :=
  state.protocolProjection_eq_log

theorem retained_record_count : retainedRecordCount = 2 := by
  rfl

end Cordis.Examples.DependentChoiceSession
