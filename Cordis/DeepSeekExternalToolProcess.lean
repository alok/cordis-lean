import Cordis.Codec
import Cordis.Tool
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
# Source-honest external tool observations

This module is the first process-backed seam for an external tool invocation.  It
records the configured command, arguments, standard output, standard error, and
exit code, then parses and decodes the observed output with a supplied dependent
codec.  A nonzero exit code is retained as evidence rather than silently turned
into a typed tool failure.

The important boundary is `accept`: an observation is untrusted data.  Only a
caller who supplies the declared `ToolSpec.post` proof can construct a
`ToolSpec.CertifiedOutcome`.  This module therefore does not claim command
identity, sandboxing, authentication, provider obedience, exactly-once effects,
cleanup, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekExternalToolProcess

universe u

open Cordis

/-! ## Process observation -/

structure ProcessConfig where
  command : String
  args : Array String := #[]
  stdin : String := ""
deriving DecidableEq, Repr

structure ProcessObservation where
  stdout : String
  stderr : String
  exitCode : UInt32
deriving DecidableEq, Repr

inductive ProcessError where
  | spawn (message : String)
deriving DecidableEq, Repr

def runProcess (config : ProcessConfig) : IO (Except ProcessError ProcessObservation) := do
  try
    let output ← IO.Process.output {
      cmd := config.command
      args := config.args
    } (some config.stdin)
    pure (.ok {
      stdout := output.stdout
      stderr := output.stderr
      exitCode := output.exitCode
    })
  catch error =>
    pure (.error (.spawn (toString error)))

/-! ## Typed decoding and postcondition acceptance -/

structure ProcessBinding
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability) where
  resultCodec : (input : spec.Input) ->
    Codec (Except (spec.Failure input) (spec.Output input))
  config : spec.Input -> ProcessConfig

inductive ObservationError where
  | process (error : ProcessError)
  | invalidJson (message : String)
  | invalidResult (error : DecodeError)
deriving DecidableEq, Repr

structure ObservedResult
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    (binding : ProcessBinding spec)
    (invocation : ToolSpec.Invocation spec) where
  config : ProcessConfig
  config_eq : config = binding.config invocation.input
  process : ProcessObservation
  json : Lean.Json
  result : Except (spec.Failure invocation.input) (spec.Output invocation.input)
  parsed : Lean.Json.parse process.stdout = .ok json
  decoded : (binding.resultCodec invocation.input).decode json = .ok result

def observe
    {Model Capability : Type}
    {spec : ToolSpec Model Capability}
    (binding : ProcessBinding spec)
    (invocation : ToolSpec.Invocation spec) :
    IO (Except ObservationError (ObservedResult (spec := spec) binding invocation)) := do
  match ← runProcess (binding.config invocation.input) with
  | .error error => pure (.error (.process error))
  | .ok process =>
      match parsed : Lean.Json.parse process.stdout with
      | .error message => pure (.error (.invalidJson message))
      | .ok json =>
          match decoded : (binding.resultCodec invocation.input).decode json with
          | .error error => pure (.error (.invalidResult error))
          | .ok result =>
              pure (.ok {
                config := binding.config invocation.input
                config_eq := rfl
                process
                json
                result
                parsed
                decoded
              })

structure AcceptedResult
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    (observed : ObservedResult binding invocation) where
  exitCode_eq_zero : observed.process.exitCode = 0
  after : Model
  postcondition : spec.post invocation.input invocation.before observed.result after

def accept
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (exitCode_eq_zero : observed.process.exitCode = 0)
    (after : Model)
    (postcondition : spec.post invocation.input invocation.before observed.result after) :
    AcceptedResult observed :=
  { exitCode_eq_zero, after, postcondition }

def AcceptedResult.certified
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (accepted : AcceptedResult observed) :
    ToolSpec.CertifiedOutcome spec invocation :=
  {
    result := observed.result
    after := accepted.after
    postcondition := accepted.postcondition
  }

theorem ObservedResult.config_exact
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    (observed : ObservedResult binding invocation) :
    observed.config = binding.config invocation.input :=
  observed.config_eq

theorem ObservedResult.result_exact
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    (observed : ObservedResult binding invocation) :
    (binding.resultCodec invocation.input).decode observed.json = .ok observed.result :=
  observed.decoded

/-! ## Deterministic fixtures -/

def echoSpec : ToolSpec Nat Unit where
  name := "echo-process"
  description := "Return the supplied string without changing the model counter."
  Input := String
  Output := fun _ => String
  Failure := fun _ => Unit
  pre := fun _ _ => True
  post := fun input before result after => after = before ∧ result = .ok input
  required := fun _ _ => False
  emission := .externalIdempotent

def echoInvocation : ToolSpec.Invocation echoSpec where
  input := "hello from cordis"
  before := 7
  granted := fun _ => True
  precondition := True.intro
  authorized := by
    intro capability required
    exact False.elim required

def echoResultCodec (input : String) :
    Codec (Except (echoSpec.Failure input) (echoSpec.Output input)) where
  schema := Lean.Json.mkObj [("type", .str "echo-result")]
  encode
    | .error _ => .arr #[.bool false, .null]
    | .ok value => .arr #[.bool true, .str value]
  decode json :=
    match json with
    | .arr values =>
        match values.toList with
        | [tag, payload] =>
            match tag, payload with
            | .bool false, .null => .ok (.error ())
            | .bool true, .str value => .ok (.ok value)
            | _, _ => .error (.typeMismatch [] "tagged echo result" .array)
        | values => .error (.invalidLength [] 2 values.length)
    | .null => .error (.typeMismatch [] "tagged echo result" .null)
    | .bool _ => .error (.typeMismatch [] "tagged echo result" .boolean)
    | .num _ => .error (.typeMismatch [] "tagged echo result" .number)
    | .str _ => .error (.typeMismatch [] "tagged echo result" .string)
    | .obj _ => .error (.typeMismatch [] "tagged echo result" .object)
  roundtrip := by
    intro result
    cases result with
    | error value => cases value <;> rfl
    | ok value => rfl

def echoBinding (body : String := "") : ProcessBinding echoSpec where
  resultCodec := echoResultCodec
  config := fun input => {
    command := "sh"
    args := #["-c", body]
    stdin := input
  }

def successfulEchoBinding : ProcessBinding echoSpec :=
  echoBinding "read input; printf '%s' '[true,\"hello from cordis\"]'"

def failingEchoBinding : ProcessBinding echoSpec :=
  echoBinding ("read input; printf '%s' '[true,\"hello from cordis\"]'; " ++
    "printf '%s' 'tool failed' 1>&2; exit 7")

theorem accepted_certified_postcondition
    {binding : ProcessBinding echoSpec}
    {observed : ObservedResult binding echoInvocation}
    (accepted : AcceptedResult observed) :
    accepted.certified.postcondition = accepted.postcondition :=
  rfl

end Cordis.DeepSeekExternalToolProcess
