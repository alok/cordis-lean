import Cordis.DeepSeekHarnessExtensionPersistence
import Cordis.SessionEventArchive

/-!
# Schedule-indexed mixed persistence certificates

`SessionRefinement` certifies the supported current-Harness core into
`Session.noExtensions`, while `SessionExtensionArchive` certifies a caller-owned
dependent extension schema.  Those APIs deliberately have different session
indices, so concatenating their certificates and calling the result one mixed
session would be unsound.  This module supplies the smallest honest composition:
an explicit row schedule, one lossless archive over the complete source list,
and two exact projection certificates over the scheduled core and extension
substreams.

The schedule is a proof-carrying source partition, not a decoder for arbitrary
mixed JSON.  It preserves exact source ASTs and both indexed endpoints, but it
does not claim that extension surface edits have been replayed into the core
protocol session, that global sequence numbers have been normalized, or that a
provider/transport/deployed persistence implementation agrees with this model.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessMixedPersistence

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionExtensionArchive
open Cordis.SessionExtensionRefinement
open Cordis.SessionRefinement

/-- Which indexed projection owns one source row. -/
inductive RowKind where
  | core
  | extension
  deriving BEq, DecidableEq, Repr

/-- Consume a schedule and the two projection lists, retaining their source order. -/
def interleave : List RowKind → List Lean.Json → List Lean.Json → List Lean.Json
  | [], _, _ => []
  | .core :: schedule, row :: coreRows, extensionRows =>
      row :: interleave schedule coreRows extensionRows
  | .extension :: schedule, coreRows, row :: extensionRows =>
      row :: interleave schedule coreRows extensionRows
  | _, _, _ => []

/-- A source-level partition whose schedule reconstructs the exact complete row stream. -/
structure MixedRows where
  input : List Lean.Json
  coreRows : List Lean.Json
  extensionRows : List Lean.Json
  schedule : List RowKind
  schedule_length : schedule.length = input.length
  split_eq : interleave schedule coreRows extensionRows = input

/-- Errors from the lossless archive or either indexed semantic projection. -/
inductive MixedPersistenceError where
  | archive (error : SessionEventArchive.ArchiveError)
  | core (error : SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
  | extension (error : SessionExtensionArchive.ArchiveExtensionError)
  deriving BEq, DecidableEq, Repr

/-- One complete mixed certificate with exact source partition and independent endpoints. -/
structure MixedCertificate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (rows : MixedRows) where
  archive : SessionEventArchive.ArchivedLog rows.input
  core : SessionRefinement.ValidatedJsonLog rows.coreRows
  extension : SessionExtensionArchive.ValidatedExtensionArchive
    codec initial rows.extensionRows

namespace MixedCertificate

/-- The lossless archive still contains exactly the complete mixed source list. -/
theorem archive_raw_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    certificate.archive.events.map SessionEventArchive.ArchivedEvent.raw = rows.input :=
  certificate.archive.raw_exact

/-- The core projection retains exactly the decoder's source list. -/
theorem core_decode_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    SessionRefinement.decodeEvents rows.coreRows = .ok certificate.core.events :=
  certificate.core.decode_eq

/-- The extension projection retains exactly the dependent codec's source list. -/
theorem extension_raw_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    certificate.extension.archive.events.map SessionEventArchive.ArchivedEvent.raw =
      rows.extensionRows :=
  certificate.extension.raw_exact

theorem core_projection_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    Session.protocolProjection certificate.core.final.session.events =
      certificate.core.sequence.protocolTrace.erase :=
  certificate.core.projection_exact

theorem extension_final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    certificate.extension.validated.final.nextSeq =
      initial.nextSeq + rows.extensionRows.length :=
  certificate.extension.final_nextSeq

theorem extension_archive_length
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {rows : MixedRows}
    (certificate : MixedCertificate codec initial rows) :
    certificate.extension.archive.events.length = rows.extensionRows.length :=
  certificate.extension.archived_length

end MixedCertificate

/-- Archive and certify both scheduled projections against the same source partition. -/
def validate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (rows : MixedRows) :
    Except MixedPersistenceError (MixedCertificate codec initial rows) :=
  match _archiveResult : SessionEventArchive.archive rows.input with
  | .error error => .error (.archive error)
  | .ok archive =>
      match _coreResult : SessionRefinement.validateJsonLog rows.coreRows with
      | .error error => .error (.core error)
      | .ok core =>
          match _extensionResult :
              SessionExtensionArchive.validate codec initial rows.extensionRows with
          | .error error => .error (.extension error)
          | .ok extension =>
              .ok { archive, core, extension }

/-! ## A concrete two-track mixed source -/

namespace Example

open SessionExtensionArchive.Example
open SessionExtensionRefinement.Example
open DeepSeekHarnessExtensions

def mixedRows : MixedRows where
  input := SessionRefinement.exampleJson ++ [heartbeatJson]
  coreRows := SessionRefinement.exampleJson
  extensionRows := [heartbeatJson]
  schedule := [.core, .core, .core, .core, .core, .core, .extension]
  schedule_length := rfl
  split_eq := rfl

def mixedCertificate :
    Except MixedPersistenceError
      (MixedCertificate exampleCodec (Session.Session.empty exampleSchema) mixedRows) :=
  validate exampleCodec (Session.Session.empty exampleSchema) mixedRows

theorem mixed_summary :
    (match mixedCertificate with
    | .error _ => none
    | .ok certificate =>
        some (
          certificate.archive.events.length,
          certificate.core.final.session.nextSeq,
          certificate.extension.validated.final.nextSeq)) =
      some (7, 6, 1) := by
  rfl

theorem mixed_schedule_exact :
    interleave mixedRows.schedule mixedRows.coreRows mixedRows.extensionRows =
      mixedRows.input :=
  mixedRows.split_eq

end Example

end Cordis.DeepSeekHarnessMixedPersistence
