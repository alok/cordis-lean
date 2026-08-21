import Cordis.DeepSeekHarness
import Cordis.RuntimeRefinement

/-!
# A bounded, proof-carrying DeepSeek tool-schema boundary

`DeepSeekApi.FunctionTool.parameters` intentionally carries a raw `Lean.Json` value. This
module adds the next type-level seam without pretending to implement all of JSON Schema:

* the parameter root must be an object schema;
* properties are a finite JSON object whose entries use one primitive `type` tag;
* property descriptions are optional strings;
* `required` is an optional duplicate-free array of names already present in `properties`;
* `additionalProperties` is an optional boolean; and
* every field outside this bounded vocabulary is rejected.

For an admitted object schema, `validateArguments` adds a second certificate: the argument JSON
must be an object with duplicate-free fields, all required names must be present, every declared
primitive value must have the matching JSON kind, and `additionalProperties: false` rejects
unknown names. This remains a deliberately shallow primitive boundary rather than full JSON
Schema validation.

Each successful certificate retains the exact source AST, every property source object, and the
request's original tool list. Thus certified request construction is a typed admission boundary,
not a claim of complete JSON-Schema semantics, provider validation, model obedience, or deployed
Harness equivalence. Nested schemas, arrays, unions, defaults, enums, constraints, and provider
extensions remain explicit unsupported cases.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekToolSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.RuntimeRefinement

/-! ## Shape vocabulary and errors -/

inductive PrimitiveSchema where
  | string
  | number
  | integer
  | boolean
  | null
deriving BEq, DecidableEq, Repr

namespace PrimitiveSchema

def wire : PrimitiveSchema -> String
  | .string => "string"
  | .number => "number"
  | .integer => "integer"
  | .boolean => "boolean"
  | .null => "null"

end PrimitiveSchema

inductive ToolSchemaError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | unsupportedField (path : List PathSegment) (name : String)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | duplicateRequired (path : List PathSegment) (name : String)
  | duplicateProperty (path : List PathSegment) (name : String)
  | unknownRequired (path : List PathSegment) (name : String)
  | duplicateToolName (name : String)
  | emptyToolName
deriving BEq, DecidableEq, Repr

private def jsonKind : Lean.Json -> JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def field? : Lean.Json -> String -> Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def indexPath (path : List PathSegment) (index : Nat) : List PathSegment :=
  path ++ [.index index]

private def decodeString (path : List PathSegment) : Lean.Json -> Except ToolSchemaError String
  | .str value => .ok value
  | value => .error (.typeMismatch path "string" (jsonKind value))

private def decodeBool (path : List PathSegment) : Lean.Json -> Except ToolSchemaError Bool
  | .bool value => .ok value
  | value => .error (.typeMismatch path "boolean" (jsonKind value))

private def optionalString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ToolSchemaError (Option String) :=
  match field? json name with
  | none => .ok none
  | some value => some <$> decodeString (fieldPath path name) value

private def optionalBool (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ToolSchemaError (Option Bool) :=
  match field? json name with
  | none => .ok none
  | some value => some <$> decodeBool (fieldPath path name) value

private def checkAllowedFields
    (path : List PathSegment)
    (allowed : List String) :
    List (String × Lean.Json) -> Except ToolSchemaError Unit
  | [] => .ok ()
  | (name, _) :: rest =>
      if name ∈ allowed then
        checkAllowedFields path allowed rest
      else
        .error (.unsupportedField (fieldPath path name) name)

structure PrimitiveCertificate (input : Lean.Json) where
  schema : PrimitiveSchema
  source_is_object : ∃ fields, input = .obj fields
  type_field : field? input "type" = some (.str schema.wire)

private def decodePrimitive (path : List PathSegment) (json : Lean.Json) :
    Except ToolSchemaError (PrimitiveCertificate json) :=
  match json with
  | .obj fields =>
      match checkAllowedFields path ["type", "description"] fields.toList with
      | .error error => .error error
      | .ok () =>
          match typeValue : fields.get? "type" with
          | none => .error (.missingField path "type")
          | some (.str "string") => .ok {
              schema := .string
              source_is_object := ⟨fields, rfl⟩
              type_field := by simpa [field?, PrimitiveSchema.wire] using typeValue
            }
          | some (.str "number") => .ok {
              schema := .number
              source_is_object := ⟨fields, rfl⟩
              type_field := by simpa [field?, PrimitiveSchema.wire] using typeValue
            }
          | some (.str "integer") => .ok {
              schema := .integer
              source_is_object := ⟨fields, rfl⟩
              type_field := by simpa [field?, PrimitiveSchema.wire] using typeValue
            }
          | some (.str "boolean") => .ok {
              schema := .boolean
              source_is_object := ⟨fields, rfl⟩
              type_field := by simpa [field?, PrimitiveSchema.wire] using typeValue
            }
          | some (.str "null") => .ok {
              schema := .null
              source_is_object := ⟨fields, rfl⟩
              type_field := by simpa [field?, PrimitiveSchema.wire] using typeValue
            }
          | some (.str other) => .error (.unsupportedTag (fieldPath path "type") other)
          | some value =>
              .error (.typeMismatch (fieldPath path "type") "string" (jsonKind value))
  | value => .error (.typeMismatch path "object schema" (jsonKind value))

/-! ## Property certificates -/

structure PropertyCertificate where
  name : String
  source : Lean.Json
  schema : PrimitiveSchema
  description : Option String
  source_is_object : ∃ fields, source = .obj fields
  type_field : field? source "type" = some (.str schema.wire)

private def decodeProperty
    (path : List PathSegment)
    (name : String)
    (json : Lean.Json) : Except ToolSchemaError { property : PropertyCertificate //
      property.name = name } := do
  match json with
  | .obj fields =>
      let schemaCertificate ← decodePrimitive (fieldPath path name) (.obj fields)
      let description ← optionalString (.obj fields) (fieldPath path name) "description"
      .ok ⟨{
          name
          source := .obj fields
          schema := schemaCertificate.schema
          description
          source_is_object := schemaCertificate.source_is_object
          type_field := schemaCertificate.type_field
        }, rfl⟩
  | value => .error (.typeMismatch (fieldPath path name) "object schema" (jsonKind value))

def propertyNames (properties : List PropertyCertificate) : List String :=
  properties.map PropertyCertificate.name

private def decodeProperties
    (path : List PathSegment) :
    List (String × Lean.Json) ->
      Except ToolSchemaError { properties : List PropertyCertificate //
        (propertyNames properties).Nodup }
  | [] => .ok ⟨[], by simp [propertyNames]⟩
  | (name, json) :: rest => do
      let property ← decodeProperty path name json
      let suffix ← decodeProperties path rest
      if duplicate : name ∈ propertyNames suffix.1 then
        .error (.duplicateProperty (fieldPath path name) name)
      else
        .ok ⟨property.1 :: suffix.1, by
          apply List.nodup_cons.mpr
          constructor
          · intro other_mem
            apply duplicate
            rw [← property.2]
            exact other_mem
          · exact suffix.2⟩

private def decodeRequiredList
    (path : List PathSegment)
    (properties : List PropertyCertificate) :
    Nat -> List Lean.Json ->
      Except ToolSchemaError
        { names : List String //
          names.Nodup ∧ ∀ name ∈ names, name ∈ propertyNames properties }
  | _, [] => .ok ⟨[], by simp⟩
  | index, value :: rest => do
      let name ← decodeString (indexPath path index) value
      let suffix ← decodeRequiredList path properties (index + 1) rest
      if duplicate : name ∈ suffix.1 then
        .error (.duplicateRequired (indexPath path index) name)
      else if present : name ∈ propertyNames properties then
        .ok ⟨name :: suffix.1, by
          constructor
          · simp only [List.nodup_cons]
            exact ⟨duplicate, suffix.2.1⟩
          · intro candidate candidate_mem
            simp only [List.mem_cons] at candidate_mem
            rcases candidate_mem with rfl | candidate_mem
            · exact by simpa using present
            · exact suffix.2.2 candidate candidate_mem⟩
      else
        .error (.unknownRequired (indexPath path index) name)

private def decodeRequired
    (path : List PathSegment)
    (properties : List PropertyCertificate)
    (json : Lean.Json) :
    Except ToolSchemaError
      { names : List String //
        names.Nodup ∧ ∀ name ∈ names, name ∈ propertyNames properties } :=
  match json with
  | .arr values => decodeRequiredList (fieldPath path "required") properties 0 values.toList
  | value => .error (.typeMismatch (fieldPath path "required") "array of strings" (jsonKind value))

structure ObjectSchema where
  source : Lean.Json
  fields : List (String × Lean.Json)
  propertiesSource : Lean.Json
  properties : List PropertyCertificate
  properties_nodup : (propertyNames properties).Nodup
  required : List String
  required_nodup : required.Nodup
  required_present : ∀ name ∈ required, name ∈ propertyNames properties
  additionalProperties : Option Bool
  type_field : field? source "type" = some (.str "object")
  properties_field : field? source "properties" = some propertiesSource

private def decodeObjectSchema (path : List PathSegment) (input : Lean.Json) :
    Except ToolSchemaError { schema : ObjectSchema // schema.source = input } :=
  match input with
  | .obj fields =>
      let json := Lean.Json.obj fields
      match checkAllowedFields path
          ["type", "properties", "required", "additionalProperties"] fields.toList with
      | .error error => .error error
      | .ok () =>
          match typeField : fields.get? "type" with
          | none => .error (.missingField path "type")
          | some (.str "object") =>
              match propertiesField : fields.get? "properties" with
              | none => .error (.missingField path "properties")
              | some (.obj propertyFields) =>
                  match decodeProperties (fieldPath path "properties") propertyFields.toList with
                  | .error error => .error error
                  | .ok properties =>
                      match field? json "required" with
                      | some requiredJson =>
                          match decodeRequired path properties.1 requiredJson with
                          | .error error => .error error
                          | .ok required =>
                              match optionalBool json path "additionalProperties" with
                              | .error error => .error error
                              | .ok additionalProperties =>
                                  .ok ⟨{
                                    source := .obj fields
                                    fields := fields.toList
                                    propertiesSource := .obj propertyFields
                                    properties := properties.1
                                    properties_nodup := properties.2
                                    required := required.1
                                    required_nodup := required.2.1
                                    required_present := required.2.2
                                    additionalProperties
                                    type_field := by simpa [field?] using typeField
                                    properties_field := by
                                      simpa [field?] using propertiesField
                                  }, rfl⟩
                      | none =>
                          match optionalBool json path "additionalProperties" with
                          | .error error => .error error
                          | .ok additionalProperties =>
                              .ok ⟨{
                                source := .obj fields
                                fields := fields.toList
                                propertiesSource := .obj propertyFields
                                properties := properties.1
                                properties_nodup := properties.2
                                required := []
                                required_nodup := by simp
                                required_present := by simp
                                additionalProperties
                                type_field := by simpa [field?] using typeField
                                properties_field := by
                                  simpa [field?] using propertiesField
                              }, rfl⟩
              | some value =>
                  .error (.typeMismatch (fieldPath path "properties") "object" (jsonKind value))
          | some (.str other) =>
              .error (.unsupportedTag (fieldPath path "type") other)
          | some value =>
              .error (.typeMismatch (fieldPath path "type") "string" (jsonKind value))
  | value => .error (.typeMismatch path "object schema" (jsonKind value))

structure ValidatedParameters (input : Lean.Json) where
  schema : ObjectSchema
  source_eq : schema.source = input

def validateParameters (input : Lean.Json) :
    Except ToolSchemaError (ValidatedParameters input) :=
  match decodeObjectSchema [] input with
  | .error error => .error error
  | .ok ⟨schema, source_eq⟩ => .ok { schema, source_eq }

namespace ValidatedParameters

def raw {input : Lean.Json} (parameters : ValidatedParameters input) : Lean.Json :=
  parameters.schema.source

theorem raw_eq {input : Lean.Json} (parameters : ValidatedParameters input) :
    parameters.raw = input :=
  parameters.source_eq

theorem required_names_present {input : Lean.Json}
    (parameters : ValidatedParameters input)
    {name : String} (name_mem : name ∈ parameters.schema.required) :
    name ∈ propertyNames parameters.schema.properties :=
  parameters.schema.required_present name name_mem

end ValidatedParameters

/-! ## Proof-carrying argument values -/

def matchesPrimitive : PrimitiveSchema -> Lean.Json -> Bool
  | .string, .str _ => true
  | .number, .num _ => true
  | .integer, .num number => number.exponent == 0
  | .boolean, .bool _ => true
  | .null, .null => true
  | _, _ => false

inductive ArgumentError where
  | invalidJson (message : String)
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingRequired (path : List PathSegment) (name : String)
  | duplicateProperty (path : List PathSegment) (name : String)
  | unknownProperty (path : List PathSegment) (name : String)
deriving BEq, DecidableEq, Repr

private def fieldNames (fields : List (String × Lean.Json)) : List String :=
  fields.map Prod.fst

private def checkArgumentFields
    (path : List PathSegment)
    (properties : List PropertyCertificate)
    (additionalProperties : Option Bool) :
    List (String × Lean.Json) ->
      Except ArgumentError { fields : List (String × Lean.Json) //
        (fieldNames fields).Nodup ∧
          (additionalProperties = some false →
            ∀ name value, (name, value) ∈ fields → name ∈ propertyNames properties) }
  | [] => .ok ⟨[], by simp [fieldNames], by simp⟩
  | (name, value) :: rest => do
      let suffix ← checkArgumentFields path properties additionalProperties rest
      if duplicate : name ∈ fieldNames suffix.1 then
        .error (.duplicateProperty (fieldPath path name) name)
      else if restrictive : additionalProperties = some false then
        if unknown : name ∉ propertyNames properties then
          .error (.unknownProperty (fieldPath path name) name)
        else
          .ok ⟨(name, value) :: suffix.1, by
            constructor
            · simpa [fieldNames] using
                (List.nodup_cons.mpr ⟨duplicate, suffix.2.1⟩)
            · intro _ candidateName candidateValue candidate_mem
              simp only [List.mem_cons] at candidate_mem
              rcases candidate_mem with candidate_mem | candidate_mem
              · cases candidate_mem
                have present : name ∈ propertyNames properties := by
                  by_cases present : name ∈ propertyNames properties
                  · exact present
                  · exact (unknown present).elim
                exact present
              · exact suffix.2.2 restrictive candidateName candidateValue candidate_mem⟩
      else
        .ok ⟨(name, value) :: suffix.1, by
          constructor
          · simpa [fieldNames] using
              (List.nodup_cons.mpr ⟨duplicate, suffix.2.1⟩)
          · intro impossible
            exact (restrictive impossible).elim⟩

private structure RequiredEvidence (json : Lean.Json) (required : List String) where
  token : Unit
  present : ∀ name, name ∈ required → ∃ value, field? json name = some value

private def checkRequired
    (path : List PathSegment)
    (json : Lean.Json) :
    (required : List String) -> Except ArgumentError
      (RequiredEvidence json required)
  | [] => .ok { token := (), present := by simp }
  | name :: rest =>
      match valueEq : field? json name with
      | none => .error (.missingRequired (fieldPath path name) name)
      | some value =>
          match checkRequired path json rest with
          | .error error => .error error
          | .ok suffix =>
              .ok {
                token := ()
                present := by
                  intro candidate candidate_mem
                  simp only [List.mem_cons] at candidate_mem
                  rcases candidate_mem with rfl | candidate_mem
                  · exact ⟨value, valueEq⟩
                  · exact suffix.present candidate candidate_mem
              }

private structure PropertyEvidence (json : Lean.Json) (properties : List PropertyCertificate) where
  token : Unit
  valid : ∀ property, property ∈ properties → ∀ value,
    field? json property.name = some value → matchesPrimitive property.schema value = true

private def checkPropertyValues
    (path : List PathSegment)
    (json : Lean.Json) :
    (properties : List PropertyCertificate) -> Except ArgumentError
      (PropertyEvidence json properties)
  | [] => .ok { token := (), valid := by simp }
  | property :: rest =>
      match valueEq : field? json property.name with
      | none =>
          match checkPropertyValues path json rest with
          | .error error => .error error
          | .ok suffix =>
              .ok {
                token := ()
                valid := by
                  intro candidate candidate_mem
                  simp only [List.mem_cons] at candidate_mem
                  rcases candidate_mem with rfl | candidate_mem
                  · intro candidateValue impossible
                    have contradiction : (none : Option Lean.Json) = some candidateValue :=
                      valueEq.symm.trans impossible
                    cases contradiction
                  · exact suffix.valid _ candidate_mem
              }
      | some value =>
          if valid : matchesPrimitive property.schema value then
            match checkPropertyValues path json rest with
            | .error error => .error error
            | .ok suffix =>
                .ok {
                  token := ()
                  valid := by
                    intro candidate candidate_mem candidateValue candidateValueEq
                    simp only [List.mem_cons] at candidate_mem
                    rcases candidate_mem with rfl | candidate_mem
                    · have value_eq : candidateValue = value := by
                        exact Option.some.inj (candidateValueEq.symm.trans valueEq)
                      cases value_eq
                      exact valid
                    · exact suffix.valid _ candidate_mem _ candidateValueEq
                }
          else
            .error (.typeMismatch (fieldPath path property.name)
              (PrimitiveSchema.wire property.schema) (jsonKind value))

structure ValidatedArguments {input : Lean.Json}
    (parameters : ValidatedParameters input) (raw : String) where
  json : Lean.Json
  parsed_eq : Lean.Json.parse raw = .ok json
  fields : List (String × Lean.Json)
  source_is_object : ∃ rawFields, json = .obj rawFields
  fields_nodup : (fieldNames fields).Nodup
  required_present : ∀ name ∈ parameters.schema.required,
    ∃ value, field? json name = some value
  properties_valid : ∀ property ∈ parameters.schema.properties,
    ∀ value, field? json property.name = some value →
      matchesPrimitive property.schema value
  unknown_properties_ok : parameters.schema.additionalProperties = some false →
    ∀ name value, (name, value) ∈ fields →
      name ∈ propertyNames parameters.schema.properties

def validateArguments {input : Lean.Json}
    (parameters : ValidatedParameters input)
    (raw : String) : Except ArgumentError (ValidatedArguments parameters raw) :=
  match parsedEq : Lean.Json.parse raw with
  | .error message => .error (.invalidJson message)
  | .ok json =>
      match json with
      | .obj fields =>
          match checkArgumentFields [] parameters.schema.properties
              parameters.schema.additionalProperties fields.toList with
          | .error error => .error error
          | .ok checkedFields =>
              match checkRequired [.field "required"] (.obj fields) parameters.schema.required with
              | .error error => .error error
              | .ok requiredPresent =>
                  match checkPropertyValues [] (.obj fields) parameters.schema.properties with
                  | .error error => .error error
                  | .ok propertiesValid =>
                      .ok {
                        json := .obj fields
                        parsed_eq := by simpa using parsedEq
                        fields := checkedFields.1
                        source_is_object := ⟨fields, rfl⟩
                        fields_nodup := checkedFields.2.1
                        required_present := requiredPresent.present
                        properties_valid := propertiesValid.valid
                        unknown_properties_ok := checkedFields.2.2
                      }
      | value => .error (.typeMismatch [] "object" (jsonKind value))

/-! ## Tool-list certificates and request construction -/

structure ValidatedToolDefinition (tool : ToolDefinition) where
  parameters : ValidatedParameters tool.function.parameters
  name_nonempty : tool.function.name ≠ ""

def validateToolDefinition (tool : ToolDefinition) :
    Except ToolSchemaError (ValidatedToolDefinition tool) :=
  if name_empty : tool.function.name = "" then
    .error .emptyToolName
  else
    match validateParameters tool.function.parameters with
    | .error error => .error error
    | .ok parameters => .ok { parameters, name_nonempty := name_empty }

namespace ValidatedToolDefinition

def validateArguments {tool : ToolDefinition}
    (certificate : ValidatedToolDefinition tool)
    (raw : String) :
    Except ArgumentError (ValidatedArguments certificate.parameters raw) :=
  DeepSeekToolSchema.validateArguments certificate.parameters raw

end ValidatedToolDefinition

inductive ValidatedToolList : List ToolDefinition -> Type where
  | nil : ValidatedToolList []
  | cons {tool : ToolDefinition} {tail : List ToolDefinition}
      (head : ValidatedToolDefinition tool)
      (tailProof : ValidatedToolList tail) : ValidatedToolList (tool :: tail)

def validateToolList :
    (tools : List ToolDefinition) -> Except ToolSchemaError (ValidatedToolList tools)
  | [] => .ok .nil
  | tool :: tail => do
      let head ← validateToolDefinition tool
      let tailProof ← validateToolList tail
      .ok (.cons head tailProof)

private def firstDuplicate : List String -> Option String
  | [] => none
  | head :: tail =>
      if head ∈ tail then some head else firstDuplicate tail

private theorem firstDuplicate_none_nodup (names : List String)
    (none_result : firstDuplicate names = none) : names.Nodup := by
  induction names with
  | nil => simp
  | cons head tail ih =>
      simp only [firstDuplicate] at none_result
      split at none_result
      · contradiction
      · exact List.nodup_cons.mpr ⟨by simpa using ‹head ∉ tail›, ih none_result⟩

structure CertifiedRequestSource (source : RequestSource) where
  tools : ValidatedToolList source.tools
  names_nodup : (source.tools.map (fun tool => tool.function.name)).Nodup

def validateRequestSource (source : RequestSource) :
    Except ToolSchemaError (CertifiedRequestSource source) :=
  match validateToolList source.tools with
  | .error error => .error error
  | .ok tools =>
      let names := source.tools.map (fun tool => tool.function.name)
      match duplicate : firstDuplicate names with
      | some name => .error (.duplicateToolName name)
      | none => .ok {
          tools
          names_nodup := firstDuplicate_none_nodup names duplicate
        }

namespace CertifiedRequestSource

def buildRequestPlan
    (baseUrl : String)
    (apiKey : ApiKey)
    {source : RequestSource}
    (_certificate : CertifiedRequestSource source)
    (session : Session.Session Session.noExtensions) :
    Except RequestError RequestPlan :=
  DeepSeekHarness.buildRequestPlan baseUrl apiKey source session

def buildTypedStreamingRequestPlan
    (baseUrl : String)
    (apiKey : ApiKey)
    {source : RequestSource}
    (_certificate : CertifiedRequestSource source)
    (session : Session.Session Session.noExtensions) :
    Except RequestError (TypedRequestPlan .streaming) :=
  DeepSeekHarness.buildTypedStreamingRequestPlan baseUrl apiKey source session

end CertifiedRequestSource

/-! ## Positive and negative kernel fixtures -/

def weatherSource : RequestSource where
  model := "deepseek-reasoner"
  system := some "Use only the certified weather tool."
  tools := [DeepSeekApi.exampleTool]
  toolChoice := some .auto

def weatherCertificate : Except ToolSchemaError (CertifiedRequestSource weatherSource) :=
  validateRequestSource weatherSource

def weatherToolCertificate :
    Except ToolSchemaError (ValidatedToolDefinition DeepSeekApi.exampleTool) :=
  validateToolDefinition DeepSeekApi.exampleTool

def malformedTool : ToolDefinition where
  function := {
    name := "bad"
    description := none
    parameters := .mkObj [
      ("type", .str "object"),
      ("properties", .mkObj [("city", .mkObj [("type", .str "date")])])
    ]
    strict := some true
  }

def malformedToolResult : Except ToolSchemaError (ValidatedToolDefinition malformedTool) :=
  validateToolDefinition malformedTool

def unknownRequiredTool : ToolDefinition where
  function := {
    name := "unknown_required"
    description := none
    parameters := .mkObj [
      ("type", .str "object"),
      ("properties", .mkObj [("city", .mkObj [("type", .str "string")])]),
      ("required", .arr #[.str "missing"])
    ]
    strict := none
  }

def unknownRequiredResult : Except ToolSchemaError
    (ValidatedToolDefinition unknownRequiredTool) :=
  validateToolDefinition unknownRequiredTool

def duplicateNamesSource : RequestSource where
  model := "duplicate-tools"
  tools := [DeepSeekApi.exampleTool, DeepSeekApi.exampleTool]

def duplicateNamesResult : Except ToolSchemaError
    (CertifiedRequestSource duplicateNamesSource) :=
  validateRequestSource duplicateNamesSource

def accepted {alpha beta : Type} : Except beta alpha -> Bool
  | .ok _ => true
  | .error _ => false

def weatherAccepted : Bool := accepted weatherCertificate

def malformedRejected : Bool := !accepted malformedToolResult

def unknownRequiredRejected : Bool := !accepted unknownRequiredResult

def duplicateNamesRejected : Bool := !accepted duplicateNamesResult

def validWeatherArgumentsAccepted : Bool :=
  match weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match certificate.validateArguments "{\"city\":\"San Francisco\"}" with
      | .ok _ => true
      | .error _ => false

def wrongWeatherArgumentsRejected : Bool :=
  match weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match certificate.validateArguments "{\"city\":3}" with
      | .ok _ => false
      | .error _ => true

def missingWeatherArgumentsRejected : Bool :=
  match weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match certificate.validateArguments "{}" with
      | .ok _ => false
      | .error _ => true

def unknownWeatherArgumentsRejected : Bool :=
  match weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match certificate.validateArguments "{\"city\":\"SF\",\"extra\":true}" with
      | .ok _ => false
      | .error _ => true

end Cordis.DeepSeekToolSchema
