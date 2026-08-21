import Cordis.RuntimeRefinement
import Cordis.RuntimeFailureRefinement

/-!
# Unified current-Harness stream outcome refinement

`RuntimeRefinement` validates the supported successful `StreamChunk` language, while
`RuntimeFailureRefinement` validates the normalized in-band `error` and `aborted` finish
language. The current Harness union needs both branches without erasing either dependent
certificate. This module is the small dispatcher at that boundary.

The dispatcher tries the successful language first and then the failure language. A successful
result contains the existing intrinsic rich-stream witness; a failure result contains the exact
ordinary prefix and every typed `LlmFailure` field. If neither language accepts the input, both
structured errors are retained. This is still a JSON-AST refinement only: it does not choose a
retry/cancellation policy, reconstruct open blocks, append a session message, authenticate a
provider, or claim equivalence with the deployed TypeScript runtime.
-/

set_option autoImplicit false

namespace Cordis.RuntimeOutcomeRefinement

open Cordis

/-! ## The disjoint dependent outcome -/

inductive OutcomeKind where
  | success
  | failure
  deriving BEq, DecidableEq, Repr

/-- Errors retained when neither supported terminal language accepts an input. -/
inductive ValidationError where
  | neither
      (success : RuntimeRefinement.ValidationError)
      (failure : RuntimeFailureRefinement.FailureDecodeError)
  deriving BEq, DecidableEq, Repr

/-- Exactly one of the supported successful or normalized failure certificates. -/
inductive ValidatedOutcome (input : List Lean.Json) where
  | success (validated : RuntimeRefinement.ValidatedJsonTrace input)
  | failure (validated : RuntimeFailureRefinement.ValidatedFailureTrace input)

namespace ValidatedOutcome

def kind {input : List Lean.Json} : ValidatedOutcome input → OutcomeKind
  | .success _ => .success
  | .failure _ => .failure

/-- The successful branch retains its exact decoded chunk equation. -/
theorem success_decode_exact
    {input : List Lean.Json}
    {validated : RuntimeRefinement.ValidatedJsonTrace input}
    (outcome : ValidatedOutcome input)
    (h : outcome = .success validated) :
    RuntimeRefinement.decodeChunks input = .ok validated.chunks := by
  cases h
  exact validated.decode_eq

/-- The failure branch retains its exact decoded prefix and terminal equation. -/
theorem failure_decode_exact
    {input : List Lean.Json}
    {validated : RuntimeFailureRefinement.ValidatedFailureTrace input}
    (outcome : ValidatedOutcome input)
    (h : outcome = .failure validated) :
    RuntimeFailureRefinement.decodeFailureTrace input =
      .ok (validated.chunks, validated.terminal) := by
  cases h
  exact validated.decoded_exact

end ValidatedOutcome

/-! ## Dispatcher -/

/-- Validate either the supported successful or normalized failure stream language. -/
def validateOutcome (input : List Lean.Json) :
    Except ValidationError (ValidatedOutcome input) :=
  match _success : RuntimeRefinement.validateJsonTrace input with
  | .ok validated => .ok (.success validated)
  | .error successError =>
      match _failure : RuntimeFailureRefinement.validateFailureTrace input with
      | .ok validated => .ok (.failure validated)
      | .error failureError => .error (.neither successError failureError)

/-! ## Exact branch equations -/

theorem validateOutcome_success
    {input : List Lean.Json}
    {validated : RuntimeRefinement.ValidatedJsonTrace input}
    (h : RuntimeRefinement.validateJsonTrace input = .ok validated) :
    validateOutcome input = .ok (.success validated) := by
  unfold validateOutcome
  rw [h]

theorem validateOutcome_failure
    {input : List Lean.Json}
    {validated : RuntimeFailureRefinement.ValidatedFailureTrace input}
    (successError : RuntimeRefinement.ValidationError)
    (success : RuntimeRefinement.validateJsonTrace input = .error successError)
    (failure : RuntimeFailureRefinement.validateFailureTrace input = .ok validated) :
    validateOutcome input = .ok (.failure validated) := by
  unfold validateOutcome
  rw [success, failure]

theorem validateOutcome_neither
    {input : List Lean.Json}
    {successError : RuntimeRefinement.ValidationError}
    {failureError : RuntimeFailureRefinement.FailureDecodeError}
    (success : RuntimeRefinement.validateJsonTrace input = .error successError)
    (failure : RuntimeFailureRefinement.validateFailureTrace input = .error failureError) :
    validateOutcome input = .error (.neither successError failureError) := by
  unfold validateOutcome
  rw [success, failure]

/-! ## Kernel-checked witnesses -/

def successfulExample : ValidatedOutcome RuntimeRefinement.exampleJson :=
  .success RuntimeRefinement.exampleJsonValidated

def failureExample : ValidatedOutcome RuntimeFailureRefinement.exampleJson :=
  .failure RuntimeFailureRefinement.exampleValidated

theorem validate_successfulExample :
    validateOutcome RuntimeRefinement.exampleJson = .ok successfulExample := by
  rfl

theorem validate_failureExample :
    validateOutcome RuntimeFailureRefinement.exampleJson = .ok failureExample := by
  rfl

theorem successfulExample_kind :
    successfulExample.kind = .success :=
  rfl

theorem failureExample_kind :
    failureExample.kind = .failure :=
  rfl

def neitherExample : List Lean.Json := [Lean.Json.mkObj [
  ("type", .str "unsupported")
]]

theorem neitherExample_rejected_by_both :
    validateOutcome neitherExample = .error (.neither
      (.decode (.unsupportedTag [.index 0, .field "type"] "unsupported"))
      (.ordinary 0 (.unsupportedTag [.field "type"] "unsupported"))) := by
  rfl

end Cordis.RuntimeOutcomeRefinement
