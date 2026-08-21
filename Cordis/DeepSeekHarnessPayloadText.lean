import Cordis.DeepSeekHarnessEventText
import Cordis.SessionPayloadArchive

/-!
# Payload-preserving text attachment for the DeepSeek Harness runner

`SessionPayloadArchive` inspects the payload objects behind the current-Harness event tags while
retaining provider-owned JSON as raw data. `DeepSeekHarnessEventText` separately restores the
semantically supported subset into a `ConversationRunner` from UTF-8/JSONL text. This module
ties those two certificates to the same parsed source: a successful value carries the enriched
payload ledger beside the restored runner, and its dependent indices force both views to describe
the same JSONL lines.

The payload pass is intentionally not a second semantic decoder. Reasoning/image blocks, usage,
tool-result error/meta values, and unknown block tags remain classified raw JSON. The runner still
requires the stricter `SessionRefinement` subset; unsupported or opaque events fail closed there.
No provider schema, logger/transport, persistence, or deployed Harness equivalence is claimed.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadText

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekSessionRunner
open Cordis.SessionPayloadArchive
open Cordis.SessionRefinement
open Cordis.TextRefinement

/-- A text restore that keeps the typed raw-payload ledger for the exact parsed lines. -/
structure RestoredPayloadRunner (source : String) where
  restored : RestoredTextRunner source
  payload : SessionPayloadArchive.PayloadLog restored.validated.parsed.lines

namespace RestoredPayloadRunner

theorem payload_raw_eq_lines
    {source : String} (restored : RestoredPayloadRunner source) :
    restored.payload.events.map SessionPayloadArchive.EnrichedEvent.raw =
      restored.restored.validated.parsed.lines := by
  exact restored.payload.raw_exact

end RestoredPayloadRunner

/-- Errors from text restoration or lossless payload archiving. -/
inductive PayloadTextError where
  | restore (error : DeepSeekHarnessEventText.TextArchiveError)
  | archive (error : SessionEventArchive.ArchiveError)
deriving DecidableEq, Repr

private theorem parse_lines_eq
    {source : String}
    {lines : List Lean.Json}
    (parsed : TextRefinement.parseJsonLines source = .ok lines)
    (restored : RestoredTextRunner source) :
    lines = restored.validated.parsed.lines := by
  exact Except.ok.inj (parsed.symm.trans restored.validated.parsed.parsed)

/-- Restore text while retaining the raw payload classification for every archived event. -/
def restoreTextPayloadRunner
    (source : String)
    (turn step : Nat) :
    Except PayloadTextError (RestoredPayloadRunner source) :=
  match parsed : TextRefinement.parseJsonLines source with
  | .error error => .error (.restore (.text error))
  | .ok lines =>
      match payloadResult : SessionPayloadArchive.archivePayload lines with
      | .error error => .error (.archive error)
      | .ok payload =>
          match restoredResult : DeepSeekHarnessEventText.restoreTextRunner source turn step with
          | .error error => .error (.restore error)
          | .ok restored => by
              have h : lines = restored.validated.parsed.lines := parse_lines_eq parsed restored
              exact .ok { restored, payload := h ▸ payload }

/-- A byte source with its exact UTF-8 decoding and payload-preserving runner. -/
structure RestoredBytesPayloadRunner (source : ByteArray) where
  text : String
  decoded : String.fromUTF8? source = some text
  restored : RestoredPayloadRunner text

/-- Decode UTF-8 bytes before retaining the same payload and runner certificates. -/
def restoreBytesPayloadRunner
    (source : ByteArray)
    (turn step : Nat) :
    Except PayloadTextError (RestoredBytesPayloadRunner source) :=
  match decoded : String.fromUTF8? source with
  | none => .error (.restore (.text .invalidUtf8))
  | some text =>
      match restoreTextPayloadRunner text turn step with
      | .error error => .error error
      | .ok result => .ok { text, decoded, restored := result }

theorem RestoredPayloadRunner.session_eq
    {source : String} (restored : RestoredPayloadRunner source) :
    restored.restored.restored.runner.session =
      restored.restored.validated.validated.final.session :=
  restored.restored.session_eq

theorem RestoredPayloadRunner.payload_length_eq
    {source : String} (restored : RestoredPayloadRunner source) :
    restored.payload.events.length = restored.payload.source.events.length :=
  restored.payload.length_eq

theorem RestoredPayloadRunner.payload_raw_exact
    {source : String} (restored : RestoredPayloadRunner source) :
    restored.payload.events.map SessionPayloadArchive.EnrichedEvent.raw =
      restored.payload.source.events.map SessionEventArchive.ArchivedEvent.raw :=
  restored.payload.raw_eq

theorem RestoredBytesPayloadRunner.decoded_eq
    {source : ByteArray} (restored : RestoredBytesPayloadRunner source) :
    String.fromUTF8? source = some restored.text :=
  restored.decoded

/-- Rebuild a request from the runner while retaining the payload ledger beside it. -/
def buildRequestCertificate
    {source : String}
    (restored : RestoredPayloadRunner source)
    (requestSource : RequestSource) :
    Except RequestError
      (DeepSeekHarnessEventArchive.RequestCertificate restored.restored.restored requestSource) :=
  DeepSeekHarnessEventText.buildRequestCertificate restored.restored requestSource

def toolPayloadTextSource : String := DeepSeekHarnessEventText.toolTextSource

def toolPayloadRestored :
    Except PayloadTextError (RestoredPayloadRunner toolPayloadTextSource) :=
  restoreTextPayloadRunner toolPayloadTextSource 1 1

def toolPayloadBytesRestored :
    Except PayloadTextError
      (RestoredBytesPayloadRunner toolPayloadTextSource.toUTF8) :=
  restoreBytesPayloadRunner toolPayloadTextSource.toUTF8 1 1

end Cordis.DeepSeekHarnessPayloadText
