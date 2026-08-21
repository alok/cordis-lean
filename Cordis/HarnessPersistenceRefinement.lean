import Cordis.SessionRefinement
import Cordis.TextRefinement
import Lean.Data.Json.Printer

/-!
# Proof-carrying Harness JSONL persistence records

The pinned DeepSeek Harness JSONL backend writes one `type: "session"` header row followed by
storage rows. A storage row is either a verbatim `SessionEvent` or one of three lossless packed
assistant-chunk rows: `text-chunks`, `reasoning-chunks`, or `tool-call-chunks`. This module models
that logical format at the JSON-AST boundary. Packed rows are validated and expanded before the
existing stateful `SessionRefinement` validator runs, so a successful result contains an exact
header/row split, exact expanded event AST, and the intrinsic append/projection certificate.

This is deliberately a logical JSONL refinement, not a filesystem or compression implementation.
Zstandard framing, byte offsets, torn-tail repair, path sanitization, coordinator concurrency,
and backend indexing remain outside. The source's packed rows use signed safe-integer timestamp
gaps; those are checked before reconstruction. Any row tag not in the three packed-row vocabulary
is retained verbatim and delegated to the session-event decoder, matching the source codec's
forward-compatible fallback.
-/

set_option autoImplicit false

namespace Cordis.HarnessPersistenceRefinement

open Cordis

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def pathField (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def pathIndex (path : List PathSegment) (index : Nat) : List PathSegment :=
  path ++ [.index index]

/-- Header metadata recognized by the pinned JSONL writer. -/
inductive HeaderOrigin where
  | subagent
  deriving BEq, DecidableEq, Repr

structure SessionHeader where
  version : Nat
  id : String
  createdAt : SafeNat
  cwd : Option String
  parentSession : Option String
  seedLength : Option SafeNat
  origin : Option HeaderOrigin
  delegationDepth : SafeNat
  agentPreset : Option String
  deriving DecidableEq, Repr

namespace SessionHeader

def originText : HeaderOrigin → String
  | .subagent => "subagent"

end SessionHeader

/-- Header errors are kept separate from event and packed-row failures. -/
inductive HeaderError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Int)
  | foreignVersion (value : Int)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | retiredField (name : String)
  deriving BEq, DecidableEq, Repr

/-- Errors in a row-tagged packed storage record. -/
inductive StorageError where
  | malformed (tag : String) (reason : String)
  | unsafeReconstruction (tag : String) (reason : String)
  deriving BEq, DecidableEq, Repr

private def requireField (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except HeaderError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def decodeString (path : List PathSegment) : Lean.Json → Except HeaderError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json → Except HeaderError SafeNat
  | .num ⟨value, 0⟩ =>
      if _h : value ≥ 0 then
        let natValue := value.toNat
        if _safe : natValue ≤ RuntimeRefinement.maxSafeInteger then
          .ok { value := natValue, safe := _safe }
        else
          .error (.unsafeInteger path value)
      else
        .error (.typeMismatch path "nonnegative safe integer" .number)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeSignedSafeInt (tag : String) (field : String) (json : Lean.Json) :
    Except StorageError Int :=
  match json with
  | .num ⟨value, 0⟩ =>
      if _safe : value.natAbs ≤ RuntimeRefinement.maxSafeInteger then
        .ok value
      else
        .error (.malformed tag (field ++ " is outside the safe integer range"))
  | _ => .error (.malformed tag (field ++ " must be an integer"))

private def decodeStorageNat (tag : String) (field : String) (json : Lean.Json) :
    Except StorageError Nat :=
  match json with
  | .num ⟨value, 0⟩ =>
      if value < 0 then
        .error (.malformed tag (field ++ " must be nonnegative"))
      else if _safe : value.toNat ≤ RuntimeRefinement.maxSafeInteger then
        .ok value.toNat
      else
        .error (.malformed tag (field ++ " is outside the safe integer range"))
  | _ => .error (.malformed tag (field ++ " must be an integer"))

private def optionalString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except HeaderError (Option String) :=
  match field? json name with
  | none => .ok none
  | some .null => .ok none
  | some value => some <$> decodeString (pathField path name) value

private def optionalNat (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except HeaderError (Option SafeNat) :=
  match field? json name with
  | none => .ok none
  | some value => some <$> decodeSafeNat (pathField path name) value

private def decodeHeader (json : Lean.Json) : Except HeaderError SessionHeader := do
  match json with
  | .obj _ => pure ()
  | value => throw (.typeMismatch [] "object" (jsonKind value))
  let typeJson ← requireField json [] "type"
  match typeJson with
  | .str "session" => pure ()
  | .str value => throw (.unsupportedTag [.field "type"] value)
  | value => throw (.typeMismatch [.field "type"] "string" (jsonKind value))
  let versionJson ← requireField json [] "version"
  let version ← match versionJson with
    | .num ⟨value, 0⟩ =>
        if value = 0 then .ok 0
        else .error (.foreignVersion value)
    | value => .error (.typeMismatch [.field "version"] "integer" (jsonKind value))
  let id ← decodeString [.field "id"] (← requireField json [] "id")
  let createdAt ← decodeSafeNat [.field "createdAt"]
    (← requireField json [] "createdAt")
  let delegationDepth ← decodeSafeNat [.field "delegationDepth"]
    (← requireField json [] "delegationDepth")
  let cwd ← optionalString json [] "cwd"
  let parentSession ← optionalString json [] "parentSession"
  let seedLength ← optionalNat json [] "seedLength"
  let origin ← match field? json "origin" with
    | none | some .null => .ok none
    | some (.str "subagent") => .ok (some .subagent)
    | some (.str value) => .error (.unsupportedTag [.field "origin"] value)
    | some value => .error (.typeMismatch [.field "origin"] "string" (jsonKind value))
  let agentPreset ← optionalString json [] "agentPreset"
  if (field? json "sandboxMode").isSome then
    throw (.retiredField "sandboxMode")
  if (field? json "approvalPolicy").isSome then
    throw (.retiredField "approvalPolicy")
  -- The upstream path library checks platform-specific absoluteness. The AST refinement retains
  -- `cwd` exactly and leaves that host filesystem predicate outside the kernel boundary.
  pure {
    version, id, createdAt, cwd, parentSession, seedLength, origin, delegationDepth, agentPreset
  }

private def hasExactKeys (json : Lean.Json) (keys : List String) : Bool :=
  match json with
  | .obj fields =>
      fields.toList.length == keys.length && keys.all (fun key => (fields.get? key).isSome)
  | _ => false

private def requireStorageField (tag : String) (json : Lean.Json) (name : String) :
    Except StorageError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.malformed tag ("missing " ++ name))

private def decodeStringList (tag : String) (field : String) (json : Lean.Json) :
    Except StorageError (List String) :=
  match json with
  | .arr values =>
      let rec loop : List Lean.Json → Except StorageError (List String)
        | [] => .ok []
        | value :: rest => do
            let text ← match value with
              | .str text => .ok text
              | _ => .error (.malformed tag (field ++ " must contain strings"))
            let suffix ← loop rest
            .ok (text :: suffix)
      loop values.toList
  | _ => .error (.malformed tag (field ++ " must be an array"))

private def decodeSignedList (tag : String) (field : String) (json : Lean.Json) :
    Except StorageError (List Int) :=
  match json with
  | .arr values =>
      let rec loop : List Lean.Json → Except StorageError (List Int)
        | [] => .ok []
        | value :: rest => do
            let gap ← decodeSignedSafeInt tag field value
            let suffix ← loop rest
            .ok (gap :: suffix)
      loop values.toList
  | _ => .error (.malformed tag (field ++ " must be an array"))

private structure RowBase where
  seq0 : Nat
  time0 : Int
  turn : Nat
  step : Nat
  index : Nat
  dt : List Int

private inductive PackedRow where
  | text (base : RowBase) (texts : List String)
  | reasoning (base : RowBase) (texts : List String)
  | toolCall (base : RowBase) (id : String) (name : Option String) (args : List String)

private def decodeRowBase (tag : String) (json : Lean.Json) : Except StorageError RowBase := do
  let seq0 ← decodeStorageNat tag "seq0" (← requireStorageField tag json "seq0")
  let time0 ← decodeSignedSafeInt tag "time0" (← requireStorageField tag json "time0")
  let data ← requireStorageField tag json "data"
  match data with
  | .obj _ => pure ()
  | _ => throw (.malformed tag "data must be an object")
  let turn ← decodeStorageNat tag "turn" (← requireStorageField tag data "turn")
  let step ← decodeStorageNat tag "step" (← requireStorageField tag data "step")
  let index ← decodeStorageNat tag "index" (← requireStorageField tag data "index")
  let dt ← decodeSignedList tag "dt" (← requireStorageField tag data "dt")
  pure { seq0, time0, turn, step, index, dt }

private def checkArity (tag : String) (dt : List Int) (payload : List String) :
    Except StorageError Unit :=
  if payload.isEmpty then
    .error (.malformed tag "payload must be nonempty")
  else if dt.length + 1 = payload.length then
    .ok ()
  else
    .error (.malformed tag "dt length must be payload length minus one")

private def safeTime (tag : String) (time : Int) : Except StorageError Unit :=
  if time.natAbs ≤ RuntimeRefinement.maxSafeInteger then
    .ok ()
  else
    .error (.unsafeReconstruction tag "reconstructed time leaves the safe integer range")

private def checkReconstruction (tag : String) (base : RowBase) (payloadLength : Nat) :
    Except StorageError Unit := do
  if base.seq0 + (payloadLength - 1) > RuntimeRefinement.maxSafeInteger then
    throw (.unsafeReconstruction tag "reconstructed sequence leaves the safe integer range")
  let rec loop : Int → List Int → Except StorageError Unit
    | _, [] => .ok ()
    | time, gap :: rest => do
        let next := time + gap
        let _ ← safeTime tag next
        loop next rest
  let _ ← safeTime tag base.time0
  loop base.time0 base.dt

private def decodePackedRow (json : Lean.Json) : Except StorageError (Option PackedRow) := do
  match json with
  | .obj _ =>
      match field? json "type" with
      | some (.str "text-chunks") =>
          let base ← decodeRowBase "text-chunks" json
          let data ← requireStorageField "text-chunks" json "data"
          if !hasExactKeys json ["type", "seq0", "time0", "data"]
              || !hasExactKeys data ["turn", "step", "index", "dt", "texts"] then
            throw (.malformed "text-chunks" "row has unexpected fields")
          let texts ← decodeStringList "text-chunks" "texts"
            (← requireStorageField "text-chunks" data "texts")
          checkArity "text-chunks" base.dt texts
          checkReconstruction "text-chunks" base texts.length
          pure (some (.text base texts))
      | some (.str "reasoning-chunks") =>
          let base ← decodeRowBase "reasoning-chunks" json
          let data ← requireStorageField "reasoning-chunks" json "data"
          if !hasExactKeys json ["type", "seq0", "time0", "data"]
              || !hasExactKeys data ["turn", "step", "index", "dt", "texts"] then
            throw (.malformed "reasoning-chunks" "row has unexpected fields")
          let texts ← decodeStringList "reasoning-chunks" "texts"
            (← requireStorageField "reasoning-chunks" data "texts")
          checkArity "reasoning-chunks" base.dt texts
          checkReconstruction "reasoning-chunks" base texts.length
          pure (some (.reasoning base texts))
      | some (.str "tool-call-chunks") =>
          let base ← decodeRowBase "tool-call-chunks" json
          let data ← requireStorageField "tool-call-chunks" json "data"
          if !hasExactKeys json ["type", "seq0", "time0", "data"] then
            throw (.malformed "tool-call-chunks" "row envelope has unexpected fields")
          let withName := hasExactKeys data ["turn", "step", "index", "id", "name", "dt", "args"]
          if !withName && !hasExactKeys data ["turn", "step", "index", "id", "dt", "args"] then
            throw (.malformed "tool-call-chunks" "row data has unexpected fields")
          let id ← match (← requireStorageField "tool-call-chunks" data "id") with
            | .str value => .ok value
            | _ => .error (.malformed "tool-call-chunks" "id must be a string")
          let name ← if withName then
            match (← requireStorageField "tool-call-chunks" data "name") with
            | .str value => .ok (some value)
            | _ => .error (.malformed "tool-call-chunks" "name must be a string")
          else
            .ok none
          let args ← decodeStringList "tool-call-chunks" "args"
            (← requireStorageField "tool-call-chunks" data "args")
          checkArity "tool-call-chunks" base.dt args
          checkReconstruction "tool-call-chunks" base args.length
          pure (some (.toolCall base id name args))
      | _ => pure none
  | _ => pure none

private def intJson (value : Int) : Lean.Json := .num ⟨value, 0⟩

private def chunkEvent (seq : Nat) (time : Int) (turn step _index : Nat)
    (chunk : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str "assistant/chunk"),
    ("seq", intJson (Int.ofNat seq)),
    ("time", intJson time),
    ("data", Lean.Json.mkObj [
      ("turn", intJson (Int.ofNat turn)),
      ("step", intJson (Int.ofNat step)),
      ("chunk", chunk)
    ])
  ]

private def expandPackedRow : PackedRow → List Lean.Json
  | .text base texts =>
      let rec loopText (seq : Nat) (time : Int) : List String → List Int → List Lean.Json
        | [], _ => []
        | text :: rest, gaps =>
            let nextTime := match gaps with | gap :: _ => time + gap | [] => time
            let tailGaps := match gaps with | _ :: suffix => suffix | [] => []
            chunkEvent seq time base.turn base.step base.index
                (Lean.Json.mkObj [
                  ("type", .str "text-delta"), ("index", intJson (Int.ofNat base.index)),
                  ("text", .str text)
                ]) :: loopText (seq + 1) nextTime rest tailGaps
      loopText base.seq0 base.time0 texts base.dt
  | .reasoning base texts =>
      let rec loopReasoning (seq : Nat) (time : Int) : List String → List Int → List Lean.Json
        | [], _ => []
        | text :: rest, gaps =>
            let nextTime := match gaps with | gap :: _ => time + gap | [] => time
            let tailGaps := match gaps with | _ :: suffix => suffix | [] => []
            chunkEvent seq time base.turn base.step base.index
                (Lean.Json.mkObj [
                  ("type", .str "reasoning-delta"), ("index", intJson (Int.ofNat base.index)),
                  ("text", .str text)
                ]) :: loopReasoning (seq + 1) nextTime rest tailGaps
      loopReasoning base.seq0 base.time0 texts base.dt
  | .toolCall base id name args =>
      let rec loopTool (seq : Nat) (time : Int) : List String → List Int → List Lean.Json
        | [], _ => []
        | arg :: rest, gaps =>
            let nextTime := match gaps with | gap :: _ => time + gap | [] => time
            let tailGaps := match gaps with | _ :: suffix => suffix | [] => []
            let chunk := Lean.Json.mkObj ([("type", .str "tool-call-delta"),
              ("index", intJson (Int.ofNat base.index)), ("id", .str id)] ++
              (match name with | some value => [("name", .str value)] | none => []) ++
              [("argumentsDelta", .str arg)])
            chunkEvent seq time base.turn base.step base.index chunk ::
              loopTool (seq + 1) nextTime rest tailGaps
      loopTool base.seq0 base.time0 args base.dt

private def expandStorageRecord (json : Lean.Json) : Except StorageError (List Lean.Json) := do
  let packed ← decodePackedRow json
  match packed with
  | some row => .ok (expandPackedRow row)
  | none => .ok [json]

private def expandStorageRecords : List Lean.Json → Except StorageError (List Lean.Json)
  | [] => .ok []
  | row :: rest => do
      let head ← expandStorageRecord row
      let tail ← expandStorageRecords rest
      .ok (head ++ tail)

/-- The exact successful logical persistence certificate. -/
structure ValidatedPersistedJson (input : List Lean.Json) where
  headerJson : Lean.Json
  header : SessionHeader
  storageRows : List Lean.Json
  expandedEvents : List Lean.Json
  split_eq : input = headerJson :: storageRows
  expansion_eq : expandStorageRecords storageRows = .ok expandedEvents
  validated : SessionRefinement.ValidatedJsonLog expandedEvents

inductive PersistenceError where
  | missingHeader
  | header (error : HeaderError)
  | storage (error : StorageError)
  | events (error : SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
  deriving BEq, DecidableEq, Repr

/-- Decode the header, expand storage rows, and run the existing stateful event refinement. -/
def validatePersistedJson (input : List Lean.Json) :
    Except PersistenceError (ValidatedPersistedJson input) :=
  match input with
  | [] => .error .missingHeader
  | headerJson :: storageRows =>
      match _decodedHeader : decodeHeader headerJson with
      | .error error => .error (.header error)
      | .ok header =>
          match expanded : expandStorageRecords storageRows with
          | .error error => .error (.storage error)
          | .ok expandedEvents =>
              match _validated : SessionRefinement.validateJsonLog expandedEvents with
              | .error error => .error (.events error)
              | .ok result => .ok {
                  headerJson, header, storageRows, expandedEvents,
                  split_eq := rfl, expansion_eq := expanded, validated := result
                }

/-- Text-level persistence validation: parse JSONL first, then preserve the logical certificate. -/
def validatePersistedText (source : String) :
    Except (TextRefinement.TextError ⊕ PersistenceError)
      (Σ input : List Lean.Json, ValidatedPersistedJson input) :=
  match _parsed : TextRefinement.parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok input =>
      match validatePersistedJson input with
      | .error error => .error (.inr error)
      | .ok result => .ok ⟨input, result⟩

namespace ValidatedPersistedJson

theorem projection_exact {input : List Lean.Json} (validated : ValidatedPersistedJson input) :
    Session.protocolProjection validated.validated.final.session.events =
      validated.validated.sequence.protocolTrace.erase :=
  validated.validated.projection_exact

theorem split_exact {input : List Lean.Json} (validated : ValidatedPersistedJson input) :
    input = validated.headerJson :: validated.storageRows :=
  validated.split_eq

theorem expansion_exact {input : List Lean.Json} (validated : ValidatedPersistedJson input) :
    expandStorageRecords validated.storageRows = .ok validated.expandedEvents :=
  validated.expansion_eq

end ValidatedPersistedJson

/-! ## Executable logical fixtures and exact rejection witnesses -/

def headerExample : Lean.Json := Lean.Json.mkObj [
  ("type", .str "session"),
  ("version", intJson 0),
  ("id", .str "session-example"),
  ("createdAt", intJson 1700000000000),
  ("cwd", .str "/work"),
  ("origin", .str "subagent"),
  ("delegationDepth", intJson 1),
  ("agentPreset", .str "default")
]

def packedTextExample : Lean.Json := Lean.Json.mkObj [
  ("type", .str "text-chunks"), ("seq0", intJson 0), ("time0", intJson 100),
  ("data", Lean.Json.mkObj [
    ("turn", intJson 1), ("step", intJson 1), ("index", intJson 0),
    ("dt", .arr #[intJson 1, intJson 2]),
    ("texts", .arr #[.str "a", .str "b", .str "c"])
  ])
]

def packedPersistenceExample : List Lean.Json := [headerExample, packedTextExample]

/-- Proof-erased observation used by executable persistence fixtures. -/
def persistenceSummary {input : List Lean.Json} :
    Except PersistenceError (ValidatedPersistedJson input) → Option (Nat × Nat × Nat)
  | .error _ => none
  | .ok validated => some (
      validated.header.version,
      validated.expandedEvents.length,
      validated.validated.final.session.nextSeq)

theorem packedPersistenceExample_valid :
    persistenceSummary (validatePersistedJson packedPersistenceExample) = some (0, 3, 3) := by
  decide

def malformedPackedRow : Lean.Json := Lean.Json.mkObj [
  ("type", .str "text-chunks"), ("seq0", intJson 0), ("time0", intJson 100),
  ("data", Lean.Json.mkObj [
    ("turn", intJson 1), ("step", intJson 0), ("index", intJson 0),
    ("dt", .arr #[]), ("texts", .arr #[.str "a", .str "b"])
  ])
]

theorem malformedPackedRow_rejected :
    persistenceSummary (validatePersistedJson [headerExample, malformedPackedRow]) = none := by
  decide

def foreignVersionHeader : Lean.Json := Lean.Json.mkObj [
  ("type", .str "session"), ("version", intJson 1),
  ("id", .str "session-example"), ("createdAt", intJson 1700000000000),
  ("delegationDepth", intJson 0)
]

theorem foreignVersion_rejected :
    persistenceSummary (validatePersistedJson [foreignVersionHeader]) = none := by
  decide

def foreignHeaderTag : Lean.Json := Lean.Json.mkObj [
  ("type", .str "event"), ("version", intJson 0),
  ("id", .str "session-example"), ("createdAt", intJson 1700000000000),
  ("delegationDepth", intJson 0)
]

theorem foreignHeaderTag_rejected :
    persistenceSummary (validatePersistedJson [foreignHeaderTag]) = none := by
  decide

end Cordis.HarnessPersistenceRefinement
