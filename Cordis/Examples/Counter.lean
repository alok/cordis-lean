import Cordis.Tool

/-!
# Certified counter tools

This deterministic example exercises request-indexed tool contracts without
claiming anything about external IO. The counter state is entirely inside the
modeled boundary, so its postconditions are genuine Lean theorems.
-/

namespace Cordis.Examples.Counter

inductive Capability where
  | read
  | write
deriving BEq, DecidableEq, Repr

inductive Operation where
  | read
  | increment
deriving BEq, DecidableEq, Repr

structure Increment where
  amount : Nat
  limit : Nat
deriving BEq, DecidableEq, Repr

def readSpec : ToolSpec Nat Capability where
  name := "counter_read"
  description := "Read the modeled counter"
  Input := Unit
  Output _ := Nat
  Failure _ := String
  pre _ _ := True
  post _ before result after :=
    match result with
    | .ok value => value = before ∧ after = before
    | .error _ => after = before
  required _ capability := capability = .read
  emission := .pure

def incrementSpec : ToolSpec Nat Capability where
  name := "counter_increment"
  description := "Increment the modeled counter without crossing the request limit"
  Input := Increment
  Output _ := Nat
  Failure _ := String
  pre input before := before + input.amount ≤ input.limit
  post input before result after :=
    match result with
    | .ok value =>
      value = before + input.amount ∧ after = value ∧ after ≤ input.limit
    | .error _ => after = before
  required _ capability := capability = .write
  emission := .internalReversible

def readTool : ToolSpec.VerifiedTool readSpec where
  execute invocation := {
    result := .ok invocation.before
    after := invocation.before
    postcondition := by simp [readSpec]
  }

def incrementTool : ToolSpec.VerifiedTool incrementSpec where
  execute invocation := {
    result := .ok (invocation.before + invocation.input.amount)
    after := invocation.before + invocation.input.amount
    postcondition := ⟨rfl, rfl, invocation.precondition⟩
  }

def catalog : ToolCatalog Nat Capability where
  Tool := Operation
  toolDecEq := inferInstance
  spec
    | .read => readSpec
    | .increment => incrementSpec

def implementation : (tool : catalog.Tool) -> ToolSpec.VerifiedTool (catalog.spec tool)
  | .read => readTool
  | .increment => incrementTool

def providerId (tool : Operation) : ProviderId := {
  domain := "example.counter"
  name := match tool with
    | .read => "read"
    | .increment => "increment"
  major := 1
}

def provider (tool : Operation) : Provider catalog.signature tool :=
  catalog.provider tool (providerId tool) (implementation tool)

/-- The example component explicitly requests both counter operations. -/
def needs : Needs catalog.signature := fun _ => True

/-- A registry containing both certified counter providers. -/
def registry : Registry catalog.signature
  | .read => some (provider .read)
  | .increment => some (provider .increment)

/-- A committed view of the example registry. -/
def view : View catalog.signature registry needs where
  resolve operation _ := by
    cases operation <;> exact { provider := provider _, present := rfl }

def readInvocation (before : Nat) : ToolSpec.Invocation readSpec where
  input := ()
  before := before
  granted capability := capability = .read
  precondition := trivial
  authorized _ required := required

def incrementInvocation
    (before : Nat)
    (input : Increment)
    (withinLimit : before + input.amount ≤ input.limit) :
    ToolSpec.Invocation incrementSpec where
  input := input
  before := before
  granted capability := capability = .write
  precondition := withinLimit
  authorized _ required := required

/-- The verified increment implementation returns the exact requested successor. -/
theorem increment_returns_requested_value
    (before : Nat)
    (input : Increment)
    (withinLimit : before + input.amount ≤ input.limit) :
    (incrementTool.execute (incrementInvocation before input withinLimit)).after =
      before + input.amount :=
  rfl

end Cordis.Examples.Counter
