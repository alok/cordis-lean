import Cordis.Codec
import Cordis.Tool

/-!
# Dynamic tool-call and result validation

Language-model output crosses the trust boundary as a textual tool name and a
`Lean.Json` AST. `validate` resolves that name, decodes the operation-specific
input, and checks precondition and authority evidence before constructing an
`AuthorizedCall`. Only that dependent call can enter `View.execute`.

Results cross the boundary in the other direction through request-indexed
codecs. A Boolean tag distinguishes failures from successes, and the resulting
`Codec` proves that every encoded typed result decodes to the same dependent
`Except` value.

Parsing bytes into `Lean.Json` remains outside this module's theorem boundary.
-/

namespace Cordis

universe u

/-- The untrusted portion of one model-produced tool call. -/
structure RawCall where
  name : String
  arguments : Lean.Json

/-- Fail-closed errors from the pure call-admission boundary. -/
inductive AdmissionError where
  | unknownTool (name : String)
  | undeclaredTool (name : String)
  | invalidArguments (name : String) (cause : DecodeError)
  | contractRejected (name reason : String)
deriving BEq, DecidableEq, Repr

/-- Constructive evidence produced by a successful admission check. -/
structure AdmissionEvidence
    {Model Capability : Type u}
    (spec : ToolSpec Model Capability)
    (input : spec.Input)
    (before : Model)
    (granted : Capability -> Prop) : Type u where
  precondition : spec.pre input before
  authorized : spec.Authorized input granted

/--
Wire metadata and a proof-producing admission check for a typed tool catalog.
`certifyAdmission` cannot return success without constructing the actual
precondition and capability propositions declared by the selected tool.
-/
structure ToolWire
    {Model Capability : Type u}
    (catalog : ToolCatalog Model Capability) where
  resolve : String -> Option catalog.Tool
  resolve_name : forall tool, resolve (catalog.spec tool).name = some tool
  inputCodec : (tool : catalog.Tool) -> Codec (catalog.spec tool).Input
  outputCodec :
    (tool : catalog.Tool) ->
    (input : (catalog.spec tool).Input) ->
    Codec ((catalog.spec tool).Output input)
  failureCodec :
    (tool : catalog.Tool) ->
    (input : (catalog.spec tool).Input) ->
    Codec ((catalog.spec tool).Failure input)
  certifyAdmission :
    (tool : catalog.Tool) ->
    (input : (catalog.spec tool).Input) ->
    (before : Model) ->
    (granted : Capability -> Prop) ->
    ((capability : Capability) -> Decidable (granted capability)) ->
    Except String (AdmissionEvidence (catalog.spec tool) input before granted)

namespace ToolWire

private def taggedResultBranchSchema
    (successful : Bool)
    (payload : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", .str "array"),
    ("prefixItems", .arr #[
      Lean.Json.mkObj [("const", .bool successful)],
      payload
    ]),
    ("minItems", .num (Lean.JsonNumber.fromNat 2)),
    ("maxItems", .num (Lean.JsonNumber.fromNat 2))
  ]

private def taggedResultSchema
    (failure output : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("oneOf", .arr #[
      taggedResultBranchSchema false failure,
      taggedResultBranchSchema true output
    ])
  ]

private def decodeTaggedResultValues
    {Failure Output : Type u}
    (failure : Codec Failure)
    (output : Codec Output) :
    List Lean.Json -> Except DecodeError (Except Failure Output)
  | [tagJson, payloadJson] =>
      match Codec.bool.decode tagJson with
      | .error error => .error (error.atIndex 0)
      | .ok false =>
          match failure.decode payloadJson with
          | .error error => .error (error.atIndex 1)
          | .ok value => .ok (.error value)
      | .ok true =>
          match output.decode payloadJson with
          | .error error => .error (error.atIndex 1)
          | .ok value => .ok (.ok value)
  | values => .error (.invalidLength [] 2 values.length)

private def decodeTaggedResult
    {Failure Output : Type u}
    (failure : Codec Failure)
    (output : Codec Output) : Lean.Json -> Except DecodeError (Except Failure Output)
  | .arr values => decodeTaggedResultValues failure output values.toList
  | .null => .error (.typeMismatch [] "tagged result array" .null)
  | .bool _ => .error (.typeMismatch [] "tagged result array" .boolean)
  | .num _ => .error (.typeMismatch [] "tagged result array" .number)
  | .str _ => .error (.typeMismatch [] "tagged result array" .string)
  | .obj _ => .error (.typeMismatch [] "tagged result array" .object)

/--
The request-dependent wire result codec. Results are represented as
`[false, failure]` or `[true, output]`; its proof concerns only `Lean.Json`
ASTs, not parsing, rendering, transport, or external schema conformance.
-/
def resultCodec
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool)
    (input : (catalog.spec tool).Input) :
    Codec (Except ((catalog.spec tool).Failure input) ((catalog.spec tool).Output input)) :=
  let failure := wire.failureCodec tool input
  let output := wire.outputCodec tool input
  {
    schema := taggedResultSchema failure.schema output.schema
    encode
      | .error value => .arr #[.bool false, failure.encode value]
      | .ok value => .arr #[.bool true, output.encode value]
    decode := decodeTaggedResult failure output
    roundtrip := by
      intro result
      cases result with
      | error value =>
          simp [decodeTaggedResult, decodeTaggedResultValues, Codec.bool, failure.roundtrip]
      | ok value =>
          simp [decodeTaggedResult, decodeTaggedResultValues, Codec.bool, output.roundtrip]
  }

/-- Encoding and decoding either branch recovers the exact dependent tool result. -/
theorem decode_encoded_result
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool)
    (input : (catalog.spec tool).Input)
    (result : Except ((catalog.spec tool).Failure input) ((catalog.spec tool).Output input)) :
    (wire.resultCodec tool input).decode ((wire.resultCodec tool input).encode result) =
      .ok result :=
  (wire.resultCodec tool input).roundtrip result

/-- Encode the actual typed result carried by a certified tool outcome. -/
def encodeCertifiedResult
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool)
    (invocation : ToolSpec.Invocation (catalog.spec tool))
    (outcome : ToolSpec.CertifiedOutcome (catalog.spec tool) invocation) : Lean.Json :=
  (wire.resultCodec tool invocation.input).encode outcome.result

/-- Encoding a certified outcome's result and decoding it recovers that exact result. -/
theorem decode_encoded_certified_result
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool)
    (invocation : ToolSpec.Invocation (catalog.spec tool))
    (outcome : ToolSpec.CertifiedOutcome (catalog.spec tool) invocation) :
    (wire.resultCodec tool invocation.input).decode
        (wire.encodeCertifiedResult tool invocation outcome) = .ok outcome.result :=
  wire.decode_encoded_result tool invocation.input outcome.result

/-- Catalog-generated input JSON always decodes to the original typed input. -/
theorem decode_encoded_input
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool)
    (input : (catalog.spec tool).Input) :
    (wire.inputCodec tool).decode ((wire.inputCodec tool).encode input) = .ok input :=
  (wire.inputCodec tool).roundtrip input

/-- Catalog operation names resolve back to the operation that owns them. -/
theorem resolve_catalog_name
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (tool : catalog.Tool) :
    wire.resolve (catalog.spec tool).name = some tool :=
  wire.resolve_name tool

/--
Validate a raw model call into a call whose request and response types are
selected by the resolved tool and whose capability membership is proved.
-/
def validate
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (needs : Needs catalog.signature)
    (needsDecidable : (tool : catalog.Tool) -> Decidable (needs tool))
    (before : Model)
    (granted : Capability -> Prop)
    (grantedDecidable : (capability : Capability) -> Decidable (granted capability))
    (raw : RawCall) :
    Except AdmissionError (AuthorizedCall catalog.signature needs) :=
  match wire.resolve raw.name with
  | none => .error (.unknownTool raw.name)
  | some tool =>
      match needsDecidable tool with
      | .isFalse _ => .error (.undeclaredTool raw.name)
      | .isTrue declared =>
          match (wire.inputCodec tool).decode raw.arguments with
          | .error error => .error (.invalidArguments raw.name error)
          | .ok input =>
              match wire.certifyAdmission tool input before granted grantedDecidable with
              | .error reason => .error (.contractRejected raw.name reason)
              | .ok evidence =>
                  let invocation : ToolSpec.Invocation (catalog.spec tool) := {
                    input := input
                    before := before
                    granted := granted
                    precondition := evidence.precondition
                    authorized := evidence.authorized
                  }
                  .ok {
                    op := tool
                    request := invocation
                    declared := declared
                  }

/-- A successfully admitted call always contains its declared-capability proof. -/
theorem validate_declared
    {Model Capability : Type u}
    {catalog : ToolCatalog Model Capability}
    (wire : ToolWire catalog)
    (needs : Needs catalog.signature)
    (needsDecidable : (tool : catalog.Tool) -> Decidable (needs tool))
    (before : Model)
    (granted : Capability -> Prop)
    (grantedDecidable : (capability : Capability) -> Decidable (granted capability))
    (raw : RawCall)
    (call : AuthorizedCall catalog.signature needs)
    (_accepted :
      validate wire needs needsDecidable before granted grantedDecidable raw = .ok call) :
    needs call.op :=
  call.declared

end ToolWire

end Cordis
