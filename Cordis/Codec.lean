import Lean.Data.Json.Basic

/-!
# Proof-carrying JSON codecs

`Codec` describes a JSON schema, an encoder, a decoder, and an AST-level proof
that decoding an encoded value succeeds with the original value.

The theorem in this module starts and ends at `Lean.Json`. Parsing bytes into a
JSON AST, rendering an AST to bytes, character encodings, transport, and storage
remain outside its trust boundary. Likewise, `schema` is descriptive metadata;
it does not prove that an external producer followed that schema.
-/

namespace Cordis

universe u v

/-- The outer JSON constructor observed when decoding fails. -/
inductive JsonKind where
  | null
  | boolean
  | number
  | string
  | array
  | object
deriving BEq, DecidableEq, Repr

/-- One step through a JSON value, from the root toward the failing node. -/
inductive PathSegment where
  | field (name : String)
  | index (index : Nat)
deriving BEq, DecidableEq, Repr

/-- Structured failures produced while decoding a JSON AST. -/
inductive DecodeError where
  /-- The node at `path` did not have the required JSON representation. -/
  | typeMismatch
      (path : List PathSegment)
      (expected : String)
      (actual : JsonKind)
  /-- A fixed-width JSON array had the wrong number of elements. -/
  | invalidLength
      (path : List PathSegment)
      (expected : Nat)
      (actual : Nat)
deriving BEq, DecidableEq, Repr

namespace DecodeError

/-- Add an outer path segment to a nested decoding error. -/
def prepend (segment : PathSegment) : DecodeError -> DecodeError
  | .typeMismatch path expected actual =>
      .typeMismatch (segment :: path) expected actual
  | .invalidLength path expected actual =>
      .invalidLength (segment :: path) expected actual

/-- Locate a nested decoding error beneath an array index. -/
def atIndex (error : DecodeError) (index : Nat) : DecodeError :=
  prepend (.index index) error

/-- Locate a nested decoding error beneath an object field. -/
def atField (error : DecodeError) (name : String) : DecodeError :=
  prepend (.field name) error

end DecodeError

/--
A JSON AST codec carrying its central correctness theorem.

`roundtrip` concerns only the in-memory `Lean.Json` representation. It makes no
claim about parsing or rendering JSON text, and it does not assert that arbitrary
external JSON satisfies `schema`.
-/
structure Codec (alpha : Type u) where
  schema : Lean.Json
  encode : alpha -> Lean.Json
  decode : Lean.Json -> Except DecodeError alpha
  roundtrip : forall value, decode (encode value) = .ok value

namespace Codec

/-- The roundtrip theorem exposed with an operation-oriented name. -/
theorem decode_encode {alpha : Type u} (codec : Codec alpha) (value : alpha) :
    codec.decode (codec.encode value) = .ok value :=
  codec.roundtrip value

private def jsonKind : Lean.Json -> JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def typeSchema (name : String) : Lean.Json :=
  Lean.Json.mkObj [("type", .str name)]

private def naturalSchema : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str "integer"),
    ("minimum", .num (Lean.JsonNumber.fromNat 0))
  ]

/-- Codec for `Unit`, represented by JSON `null`. -/
def unit : Codec Unit where
  schema := typeSchema "null"
  encode := fun _ => .null
  decode
    | .null => .ok ()
    | json => .error (.typeMismatch [] "null" (jsonKind json))
  roundtrip := by
    intro value
    cases value
    rfl

/-- Codec for JSON booleans. -/
def bool : Codec Bool where
  schema := typeSchema "boolean"
  encode := .bool
  decode
    | .bool value => .ok value
    | json => .error (.typeMismatch [] "boolean" (jsonKind json))
  roundtrip := by
    intro value
    rfl

/-- Codec for JSON strings. -/
def string : Codec String where
  schema := typeSchema "string"
  encode := .str
  decode
    | .str value => .ok value
    | json => .error (.typeMismatch [] "string" (jsonKind json))
  roundtrip := by
    intro value
    rfl

private def decodeNat : Lean.Json -> Except DecodeError Nat
  | .num ⟨Int.ofNat value, 0⟩ => .ok value
  | json =>
      .error (.typeMismatch [] "nonnegative integer" (jsonKind json))

/-- Codec for natural numbers in canonical, exponent-zero JSON representation. -/
def nat : Codec Nat where
  schema := naturalSchema
  encode := fun value => .num (Lean.JsonNumber.fromNat value)
  decode := decodeNat
  roundtrip := by
    intro value
    rfl

private def productSchema (left right : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str "array"),
    ("prefixItems", .arr #[left, right]),
    ("minItems", .num (Lean.JsonNumber.fromNat 2)),
    ("maxItems", .num (Lean.JsonNumber.fromNat 2))
  ]

private def decodeProdValues
    {alpha : Type u}
    {beta : Type v}
    (left : Codec alpha)
    (right : Codec beta) : List Lean.Json -> Except DecodeError (alpha × beta)
  | [leftJson, rightJson] =>
      match left.decode leftJson with
      | .error error => .error (error.atIndex 0)
      | .ok leftValue =>
          match right.decode rightJson with
          | .error error => .error (error.atIndex 1)
          | .ok rightValue => .ok (leftValue, rightValue)
  | values => .error (.invalidLength [] 2 values.length)

private def decodeProd
    {alpha : Type u}
    {beta : Type v}
    (left : Codec alpha)
    (right : Codec beta) : Lean.Json -> Except DecodeError (alpha × beta)
  | .arr values => decodeProdValues left right values.toList
  | json => .error (.typeMismatch [] "two-element array" (jsonKind json))

/-- Product codec, represented by a two-element JSON array. -/
def prod
    {alpha : Type u}
    {beta : Type v}
    (left : Codec alpha)
    (right : Codec beta) : Codec (alpha × beta) where
  schema := productSchema left.schema right.schema
  encode := fun value => .arr #[left.encode value.1, right.encode value.2]
  decode := decodeProd left right
  roundtrip := by
    intro value
    rcases value with ⟨leftValue, rightValue⟩
    simp [decodeProd, decodeProdValues, left.roundtrip, right.roundtrip]

private def listSchema (item : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str "array"),
    ("items", item)
  ]

private def decodeValues
    {alpha : Type u}
    (item : Codec alpha) :
    Nat -> List Lean.Json -> Except DecodeError (List alpha)
  | _, [] => .ok []
  | index, json :: rest =>
      match item.decode json with
      | .error error => .error (error.atIndex index)
      | .ok value =>
          match decodeValues item (index + 1) rest with
          | .error error => .error error
          | .ok values => .ok (value :: values)

private theorem decodeValues_encode
    {alpha : Type u}
    (item : Codec alpha)
    (index : Nat)
    (values : List alpha) :
    decodeValues item index (values.map item.encode) = .ok values := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail ih =>
      simp [decodeValues, item.roundtrip, ih]

private def decodeList
    {alpha : Type u}
    (item : Codec alpha) : Lean.Json -> Except DecodeError (List alpha)
  | .arr values => decodeValues item 0 values.toList
  | json => .error (.typeMismatch [] "array" (jsonKind json))

/-- List codec, represented by a JSON array with path-aware element errors. -/
def list {alpha : Type u} (item : Codec alpha) : Codec (List alpha) where
  schema := listSchema item.schema
  encode := fun values => .arr (values.map item.encode).toArray
  decode := decodeList item
  roundtrip := by
    intro values
    simp [decodeList, decodeValues_encode]

end Codec

end Cordis
