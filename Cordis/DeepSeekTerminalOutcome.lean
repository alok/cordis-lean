import Cordis.DeepSeekStreamFailure
import Cordis.DeepSeekRichStream
import Cordis.DeepSeekRichToolStream
import Cordis.DeepSeekRichMixedStream
import Cordis.DeepSeekRichMultiStream

/-!
# A proof-carrying terminal DeepSeek stream outcome

The individual DeepSeek projectors deliberately recognize different disjoint
wire languages. `DeepSeekStreamFailure` recognizes provider terminal failures;
the rich projectors recognize successful text, tool, mixed, and multi-call
traces. This module composes those validators without erasing their dependent
certificates. A body is accepted only when one complete language accepts it,
and a rejected body retains the exact wire or projection reason from the last
language that was applicable.

This is still a complete-body validator, not a live transport or deployed
provider model. It does not claim retry, cancellation, byte-level framing,
backpressure, assembler equivalence, session-message construction, or support
for wire-level error/aborted envelopes outside `DeepSeekStream`.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekTerminalOutcome

open Cordis
open Cordis.DeepSeekRichMixedStream
open Cordis.DeepSeekRichMultiStream
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekRichToolStream
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamFailure

inductive TerminalOutcomeError where
  | wire (error : StreamError)
  | failure (error : FailureProjectionError)
  | text (error : DeepSeekRichStream.ProjectionError)
  | tool (error : DeepSeekRichToolStream.ProjectionError)
  | mixed (error : DeepSeekRichMixedStream.ProjectionError)
  | multi (error : DeepSeekRichMultiStream.ProjectionError)
deriving DecidableEq, Repr

inductive TerminalOutcome (body : String) where
  | failure (validated : ValidatedFailureStream body)
  | text (validated : ValidatedTextStream body)
  | tool (validated : ValidatedToolStream body)
  | mixed (validated : ValidatedMixedStream body)
  | multi (validated : ValidatedMultiStream body)

inductive Kind where
  | providerFailure
  | text
  | tool
  | mixed
  | multi
deriving DecidableEq, Repr

def TerminalOutcome.kind {body : String} : TerminalOutcome body → Kind
  | .failure _ => .providerFailure
  | .text _ => .text
  | .tool _ => .tool
  | .mixed _ => .mixed
  | .multi _ => .multi

private def validateTextAfterFailure (body : String) :
    Except TerminalOutcomeError (TerminalOutcome body) :=
  match DeepSeekRichStream.validateTextStream body with
  | .ok validated => .ok (.text validated)
  | .error (.wire error) => .error (.wire error)
  | .error (.projection _error) =>
      match DeepSeekRichToolStream.validateToolStream body with
      | .ok validated => .ok (.tool validated)
      | .error (.wire error) => .error (.wire error)
      | .error (.projection _toolError) =>
          match DeepSeekRichMixedStream.validateMixedStream body with
          | .ok validated => .ok (.mixed validated)
          | .error (.wire error) => .error (.wire error)
          | .error (.projection _mixedError) =>
              match DeepSeekRichMultiStream.validateMultiStream body with
              | .ok validated => .ok (.multi validated)
              | .error (.wire error) => .error (.wire error)
              | .error (.projection multiError) =>
                  .error (.multi multiError)

def validateTerminalOutcome (body : String) :
    Except TerminalOutcomeError (TerminalOutcome body) :=
  match DeepSeekStreamFailure.validateFailureStream body with
  | .ok validated => .ok (.failure validated)
  | .error (.inl error) => .error (.wire error)
  | .error (.inr _error) =>
      match validateTextAfterFailure body with
      | .ok validated => .ok validated
      | .error terminalError =>
          match terminalError with
          | .wire error => .error (.wire error)
          | .text projection => .error (.text projection)
          | .tool projection => .error (.tool projection)
          | .mixed projection => .error (.mixed projection)
          | .multi projection => .error (.multi projection)
          | .failure failureError => .error (.failure failureError)

theorem validateTerminalOutcome_failure
    {body : String} {validated : ValidatedFailureStream body}
    (h : DeepSeekStreamFailure.validateFailureStream body = .ok validated) :
    validateTerminalOutcome body = .ok (.failure validated) := by
  simp [validateTerminalOutcome, h]

theorem validateTerminalOutcome_text
    {body : String} {failureError : FailureProjectionError}
    (failure : DeepSeekStreamFailure.validateFailureStream body = .error (.inr failureError))
    {validated : ValidatedTextStream body}
    (text : DeepSeekRichStream.validateTextStream body = .ok validated) :
    validateTerminalOutcome body = .ok (.text validated) := by
  simp [validateTerminalOutcome, validateTextAfterFailure, failure, text]

theorem validateTerminalOutcome_tool
    {body : String} {failureError : FailureProjectionError}
    (failure : DeepSeekStreamFailure.validateFailureStream body = .error (.inr failureError))
    {textError : DeepSeekRichStream.ProjectionError}
    (text : DeepSeekRichStream.validateTextStream body = .error (.projection textError))
    {validated : ValidatedToolStream body}
    (tool : DeepSeekRichToolStream.validateToolStream body = .ok validated) :
    validateTerminalOutcome body = .ok (.tool validated) := by
  simp [validateTerminalOutcome, validateTextAfterFailure, failure, text, tool]

def exampleFailure : Except TerminalOutcomeError
    (TerminalOutcome DeepSeekStreamFailure.exampleContentFilterBody) :=
  validateTerminalOutcome DeepSeekStreamFailure.exampleContentFilterBody

def exampleText : Except TerminalOutcomeError
    (TerminalOutcome DeepSeekRichStream.exampleTextStreamBody) :=
  validateTerminalOutcome DeepSeekRichStream.exampleTextStreamBody

def exampleTool : Except TerminalOutcomeError
    (TerminalOutcome DeepSeekRichToolStream.exampleToolStreamBody) :=
  validateTerminalOutcome DeepSeekRichToolStream.exampleToolStreamBody

def exampleMixed : Except TerminalOutcomeError
    (TerminalOutcome DeepSeekRichMixedStream.mixedStreamBody) :=
  validateTerminalOutcome DeepSeekRichMixedStream.mixedStreamBody

def exampleMulti : Except TerminalOutcomeError
    (TerminalOutcome DeepSeekRichMultiStream.multiBody) :=
  validateTerminalOutcome DeepSeekRichMultiStream.multiBody

end Cordis.DeepSeekTerminalOutcome
