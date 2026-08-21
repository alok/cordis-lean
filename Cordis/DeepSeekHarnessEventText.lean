import Cordis.DeepSeekHarnessEventArchive
import Cordis.TextRefinement

/-!
# Text and UTF-8 attachment for the current-Harness event archive

`DeepSeekHarnessEventArchive` restores a typed `ConversationRunner` from a supported
current-Harness event archive whose input is already a `List Lean.Json`. This module adds the
adjacent text boundary: it parses canonical JSONL text or UTF-8 bytes, keeps the decoded source
and parser certificate, and then attaches the validated event archive to the same runner.

The result is deliberately proof-carrying. A restored value retains the parsed lines, the
stateful `SessionRefinement` certificate, the lossless `SessionEventArchive` certificate, and
the equality identifying the runner session with the validated endpoint. A request certificate
can therefore be built from the restored runner without reparsing or dropping the source AST.
Invalid UTF-8, malformed JSONL, unsupported session payloads, required opaque events, and
request-builder failures remain typed boundaries. This does not claim deployed logger/schema
compatibility, persistence, crash recovery, or whole-runtime equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventText

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventArchive
open Cordis.DeepSeekSessionRunner
open Cordis.SessionEventArchive
open Cordis.SessionRefinement
open Cordis.TextRefinement

/-- Errors at the text, archive, or stateful session-validation boundary. -/
inductive TextArchiveError where
  | text (error : TextError)
  | archive (error : SessionEventArchive.ArchiveError)
  | validation (error : SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
  | opaqueRequired
deriving DecidableEq, Repr

/-- A validated text session whose supported event archive is attached to a runner. -/
structure RestoredTextRunner (source : String) where
  validated : TextRefinement.ValidatedSessionText source
  restored : DeepSeekHarnessEventArchive.RestoredRunner validated.parsed.lines
  log_validated_eq : restored.log.validated = validated.validated

private def restoreParsed
    {source : String}
    (parsed : TextRefinement.ParsedText source)
    (archive : SessionEventArchive.ArchivedLog parsed.lines)
    (validated : SessionRefinement.ValidatedJsonLog parsed.lines)
    (turn step : Nat) :
    Except TextArchiveError (RestoredTextRunner source) :=
  if supported : ∀ event ∈ archive.events, event.isOpaque = false then
    let textValidated : TextRefinement.ValidatedSessionText source := {
      parsed
      validated
    }
    let log : DeepSeekHarnessEventArchive.SupportedEventLog parsed.lines := {
      archive
      validated
      supported
    }
    .ok {
      validated := textValidated
      restored := DeepSeekHarnessEventArchive.restoreRunner log turn step
        (toolCallCount validated.final.session.messages) rfl
      log_validated_eq := rfl
    }
  else
    .error .opaqueRequired

private def restoreParsedAfterArchive
    {source : String}
    (parsed : TextRefinement.ParsedText source)
    (archive : SessionEventArchive.ArchivedLog parsed.lines)
    (turn step : Nat) :
    Except TextArchiveError (RestoredTextRunner source) :=
  match _validatedResult : SessionRefinement.validateJsonLog parsed.lines with
  | .error error => .error (.validation error)
  | .ok validated => restoreParsed parsed archive validated turn step

private def restoreParsedText
    {source : String}
    (parsed : TextRefinement.ParsedText source)
    (turn step : Nat) :
    Except TextArchiveError (RestoredTextRunner source) :=
  match _archiveResult : SessionEventArchive.archive parsed.lines with
  | .error error => .error (.archive error)
  | .ok archive => restoreParsedAfterArchive parsed archive turn step

/-- Parse canonical JSONL text and restore its supported current-Harness runner. -/
def restoreTextRunner
    (source : String)
    (turn step : Nat) :
    Except TextArchiveError (RestoredTextRunner source) :=
  match parsedResult : TextRefinement.parseJsonLines source with
  | .error error => .error (.text error)
  | .ok lines =>
      restoreParsedText { lines, parsed := parsedResult } turn step

/-- A UTF-8 source together with its decoded text and restored event runner. -/
structure RestoredBytesRunner (source : ByteArray) where
  text : String
  decoded : String.fromUTF8? source = some text
  restored : RestoredTextRunner text

/-- Decode UTF-8 bytes and restore the supported current-Harness event runner. -/
def restoreBytesRunner
    (source : ByteArray)
    (turn step : Nat) :
    Except TextArchiveError (RestoredBytesRunner source) :=
  match decoded : String.fromUTF8? source with
  | none => .error (.text .invalidUtf8)
  | some text =>
      match _result : restoreTextRunner text turn step with
      | .error error => .error error
      | .ok restored => .ok { text, decoded, restored }

theorem RestoredTextRunner.source_parse_eq
    {source : String} (restored : RestoredTextRunner source) :
    TextRefinement.parseJsonLines source = .ok restored.validated.parsed.lines :=
  restored.validated.parsed.parsed

theorem RestoredTextRunner.session_eq
    {source : String} (restored : RestoredTextRunner source) :
    restored.restored.runner.session = restored.validated.validated.final.session :=
  by rw [← restored.log_validated_eq]; exact restored.restored.session_eq

theorem RestoredTextRunner.archive_raw_eq_lines
    {source : String} (restored : RestoredTextRunner source) :
    restored.restored.log.archive.events.map ArchivedEvent.raw =
      restored.validated.parsed.lines :=
  restored.restored.archive_raw_eq_input

theorem RestoredBytesRunner.decoded_eq
    {source : ByteArray} (restored : RestoredBytesRunner source) :
    String.fromUTF8? source = some restored.text :=
  restored.decoded

/-- Reuse the event-archive request certificate after text/bytes restoration. -/
def buildRequestCertificate
    {source : String}
    (restored : RestoredTextRunner source)
    (requestSource : RequestSource) :
    Except RequestError
      (DeepSeekHarnessEventArchive.RequestCertificate restored.restored requestSource) :=
  DeepSeekHarnessEventArchive.buildRequestCertificate restored.restored requestSource

def toolTextSource : String :=
  TextRefinement.renderJsonLines SessionRefinement.toolMessageExampleJson

def toolTextRestored :
    Except TextArchiveError (RestoredTextRunner toolTextSource) :=
  restoreTextRunner toolTextSource 1 1

def toolBytesRestored :
    Except TextArchiveError (RestoredBytesRunner toolTextSource.toUTF8) :=
  restoreBytesRunner toolTextSource.toUTF8 1 1

end Cordis.DeepSeekHarnessEventText
