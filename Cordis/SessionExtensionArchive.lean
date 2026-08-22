import Cordis.SessionEventArchive
import Cordis.SessionExtensionRefinement

/-!
# Lossless archive attachment for typed extension sequences

`SessionEventArchive` deliberately retains unknown extension envelopes as opaque records, while
`SessionExtensionRefinement` can validate a caller-owned dependent extension family.  This module
joins those two boundaries without guessing a payload: a successful result contains the complete
lossless archive, a sequential dependent replay over the same raw list, and a proof that every
archived record is a required extension rather than a known core event or an ignorable record.

The bridge is intentionally extension-only.  It does not claim that a mixed current-Harness log
can be replayed by one extension codec, and it does not turn archive retention into persistence,
provider compatibility, transport trust, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.SessionExtensionArchive

open Cordis
open Cordis.SessionEventArchive
open Cordis.SessionExtensionRefinement

/-- Errors from the lossless-archive plus dependent-extension replay boundary. -/
inductive ArchiveExtensionError where
  | archive (error : SessionEventArchive.ArchiveError)
  | notExtension (index : Nat) (tag : Option SessionEventArchive.KnownTag)
  | ignorable (index : Nat)
  | semantic (error : ExtensionDecodeError)
  deriving BEq, DecidableEq, Repr

private structure EventCertification
    (events : List SessionEventArchive.ArchivedEvent) where
  token : Unit
  required_extensions :
    ∀ event, event ∈ events →
      event.tag? = none ∧ event.isRequired = true

private def certifyEvents :
    (index : Nat) →
    (events : List SessionEventArchive.ArchivedEvent) →
    Except ArchiveExtensionError (EventCertification events)
  | _, [] => .ok {
      token := ()
      required_extensions := by
        intro event membership
        cases membership
    }
  | index, head :: tail =>
      if tag : head.tag? = none then
        if required : head.isRequired = true then
          match tailResult : certifyEvents (index + 1) tail with
          | .error error => .error error
          | .ok tailProof =>
              .ok {
                token := ()
                required_extensions := by
                  intro event membership
                  simp only [List.mem_cons] at membership
                  cases membership with
                  | inl headEq =>
                      subst event
                      exact ⟨tag, required⟩
                  | inr tailMembership =>
                      exact tailProof.required_extensions event tailMembership
              }
        else
          .error (.ignorable index)
      else
        .error (.notExtension index head.tag?)

/-- Archive and dependent replay certificates over one exact raw extension list. -/
structure ValidatedExtensionArchive
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) where
  archive : SessionEventArchive.ArchivedLog input
  validated : ValidatedExtensionLog codec initial input
  required_extensions :
    ∀ event, event ∈ archive.events →
      event.tag? = none ∧ event.isRequired = true

namespace ValidatedExtensionArchive

theorem raw_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (archive : ValidatedExtensionArchive codec initial input) :
    archive.archive.events.map ArchivedEvent.raw = input :=
  archive.archive.raw_eq

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (archive : ValidatedExtensionArchive codec initial input) :
    archive.validated.final.nextSeq = initial.nextSeq + input.length :=
  archive.validated.final_nextSeq

theorem typed_event_count
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (archive : ValidatedExtensionArchive codec initial input) :
    archive.validated.replay.events.length = input.length :=
  archive.validated.typed_event_count

theorem archived_length
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (archive : ValidatedExtensionArchive codec initial input) :
    archive.archive.events.length = input.length :=
  archive.archive.length_eq

end ValidatedExtensionArchive

/-- Validate the lossless archive and the dependent replay against the same input list. -/
def validate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) :
    Except ArchiveExtensionError (ValidatedExtensionArchive codec initial input) :=
  match _archiveResult : SessionEventArchive.archive input with
  | .error error => .error (.archive error)
  | .ok archive =>
      match _certifiedResult : certifyEvents 0 archive.events with
      | .error error => .error error
      | .ok requiredExtensions =>
          match _validatedResult : SessionExtensionRefinement.validate codec initial input with
          | .error error => .error (.semantic error)
          | .ok validated =>
              .ok {
                archive,
                validated,
                required_extensions := requiredExtensions.required_extensions
              }

namespace Example

open SessionExtensionRefinement.Example
open DeepSeekHarnessExtensions

def archivedExample :
    Except ArchiveExtensionError
      (ValidatedExtensionArchive exampleCodec
        (Session.Session.empty exampleSchema) exampleInput) :=
  validate exampleCodec (Session.Session.empty exampleSchema) exampleInput

theorem archived_example_summary :
    (match archivedExample with
    | .error _ => none
    | .ok archive =>
        some (
          archive.validated.final.nextSeq,
          archive.archive.events.length,
          archive.validated.replay.events.length)) =
      some (2, 2, 2) := by
  rfl

theorem archived_example_raw_exact :
    (match archivedExample with
    | .error _ => []
    | .ok archive => archive.archive.events.map ArchivedEvent.raw) = exampleInput := by
  rfl

theorem archived_example_required_extensions :
    (match archivedExample with
    | .error _ => false
    | .ok archive =>
        archive.archive.events.all (fun event =>
          event.tag?.isNone && event.isRequired)) =
      true := by
  rfl

def knownCoreJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "turn/start"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("data", Lean.Json.mkObj [("turn", .num 0)])
]

def ignorableExtensionJson : Lean.Json := Lean.Json.mkObj [
  ("type", .str "cordis/extension"),
  ("seq", .num (Lean.JsonNumber.fromNat 0)),
  ("time", .num (Lean.JsonNumber.fromNat 100)),
  ("ignorable", .bool true),
  ("data", Lean.Json.mkObj [("kind", .str "heartbeat")])
]

theorem reject_known_core :
    validate exampleCodec (Session.Session.empty exampleSchema) [knownCoreJson] =
      .error (.notExtension 0 (some .turnStart)) := by
  rfl

theorem reject_ignorable_extension :
    validate exampleCodec (Session.Session.empty exampleSchema) [ignorableExtensionJson] =
      .error (.ignorable 0) := by
  rfl

end Example

end Cordis.SessionExtensionArchive
