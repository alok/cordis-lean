import Cordis.Codec
import Cordis.Tool

/-!
# Dynamic tool-call validation

Language-model output crosses the trust boundary as a textual tool name and a
`Lean.Json` AST. `validate` resolves that name, decodes the operation-specific
input, and checks precondition and authority evidence before constructing an
`AuthorizedCall`. Only that dependent call can enter `View.execute`.

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
`admit` cannot return success without constructing the actual precondition and
capability propositions declared by the selected tool.
-/
structure ToolWire
    {Model Capability : Type u}
    (catalog : ToolCatalog Model Capability) where
  resolve : String -> Option catalog.Tool
  resolve_name : forall tool, resolve (catalog.spec tool).name = some tool
  inputCodec : (tool : catalog.Tool) -> Codec (catalog.spec tool).Input
  admit :
    (tool : catalog.Tool) ->
    (input : (catalog.spec tool).Input) ->
    (before : Model) ->
    (granted : Capability -> Prop) ->
    ((capability : Capability) -> Decidable (granted capability)) ->
    Except String (AdmissionEvidence (catalog.spec tool) input before granted)

namespace ToolWire

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
              match wire.admit tool input before granted grantedDecidable with
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
