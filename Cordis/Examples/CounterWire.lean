import Cordis.Examples.Counter
import Cordis.ToolWire

/-!
# Counter wire boundary

This module turns raw model calls into the certified counter API. It is a small
executable example of the checked-to-proved boundary: name resolution, JSON
decoding, the counter limit, and capability grants must all succeed before an
`AuthorizedCall` exists.
-/

namespace Cordis.Examples.Counter

private def incrementPairCodec : Codec (Nat × Nat) :=
  Codec.prod Codec.nat Codec.nat

def incrementCodec : Codec Increment where
  schema := incrementPairCodec.schema
  encode input := incrementPairCodec.encode (input.amount, input.limit)
  decode json :=
    match incrementPairCodec.decode json with
    | .error error => .error error
    | .ok pair => .ok { amount := pair.1, limit := pair.2 }
  roundtrip := by
    intro input
    change
      (match incrementPairCodec.decode
          (incrementPairCodec.encode (input.amount, input.limit)) with
        | .error error => Except.error error
        | .ok pair => Except.ok { amount := pair.1, limit := pair.2 }) =
          Except.ok input
    rw [incrementPairCodec.roundtrip]

private def resolveTool : String -> Option Operation
  | "counter_read" => some .read
  | "counter_increment" => some .increment
  | _ => none

private def certifyReadAdmission
    (before : Nat)
    (granted : Capability -> Prop)
    (grantedDecidable : (capability : Capability) -> Decidable (granted capability)) :
    Except String (AdmissionEvidence readSpec () before granted) :=
  match grantedDecidable .read with
  | .isTrue hasRead =>
      .ok {
        precondition := trivial
        authorized := by
          intro capability required
          change capability = Capability.read at required
          subst capability
          exact hasRead
      }
  | .isFalse _ => .error "counter_read requires the read capability"

private def certifyIncrementAdmission
    (input : Increment)
    (before : Nat)
    (granted : Capability -> Prop)
    (grantedDecidable : (capability : Capability) -> Decidable (granted capability)) :
    Except String (AdmissionEvidence incrementSpec input before granted) :=
  if withinLimit : before + input.amount ≤ input.limit then
    match grantedDecidable .write with
    | .isTrue hasWrite =>
        .ok {
          precondition := withinLimit
          authorized := by
            intro capability required
            change capability = Capability.write at required
            subst capability
            exact hasWrite
        }
    | .isFalse _ => .error "counter_increment requires the write capability"
  else
    .error "counter_increment would cross the request limit"

def wire : ToolWire catalog where
  resolve := resolveTool
  resolve_name tool := by cases tool <;> rfl
  inputCodec
    | .read => Codec.unit
    | .increment => incrementCodec
  outputCodec
    | .read, () => Codec.nat
    | .increment, _ => Codec.nat
  failureCodec
    | .read, () => Codec.string
    | .increment, _ => Codec.string
  certifyAdmission
    | .read, (), before, granted, decideGranted =>
        certifyReadAdmission before granted decideGranted
    | .increment, input, before, granted, decideGranted =>
        certifyIncrementAdmission input before granted decideGranted

def allNeeds : Needs catalog.signature := fun _ => True

def allNeedsDecidable (tool : Operation) : Decidable (allNeeds tool) :=
  isTrue trivial

def allCapabilities : Capability -> Prop := fun _ => True

def allCapabilitiesDecidable
    (capability : Capability) : Decidable (allCapabilities capability) :=
  isTrue trivial

/-- Validate a raw counter call with the deterministic example's full capability set. -/
def validateRaw
    (before : Nat)
    (raw : RawCall) : Except AdmissionError (AuthorizedCall catalog.signature allNeeds) :=
  wire.validate allNeeds allNeedsDecidable before allCapabilities
    allCapabilitiesDecidable raw

def rawRead : RawCall where
  name := readSpec.name
  arguments := Codec.unit.encode ()

def readCall (before : Nat) : AuthorizedCall catalog.signature allNeeds := {
  op := .read
  request := {
    input := ()
    before := before
    granted := allCapabilities
    precondition := trivial
    authorized := by
      intro capability required
      exact trivial
  }
  declared := trivial
}

theorem validateRaw_read (before : Nat) :
    validateRaw before rawRead = .ok (readCall before) := by
  simp [validateRaw, ToolWire.validate, rawRead, readCall, wire, resolveTool,
    readSpec, Codec.unit,
    certifyReadAdmission, allCapabilities, allCapabilitiesDecidable,
    allNeedsDecidable]

def rawIncrement (input : Increment) : RawCall where
  name := incrementSpec.name
  arguments := incrementCodec.encode input

def rawUnknown : RawCall where
  name := "counter_destroy"
  arguments := .null

end Cordis.Examples.Counter
