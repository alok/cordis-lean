/-!
# Dependent API signatures

This module is the formal center of CORDIS Lean's "API as type signature"
design. An operation selects both its request type and the response type for
that particular request. Components receive a `View` restricted by a `Needs`
predicate rather than an ambient registry.
-/

namespace Cordis

universe u v w

/-- A universe of operations with request-indexed response types. -/
structure Signature where
  Op : Type u
  opDecEq : DecidableEq Op
  Request : Op -> Type v
  Response : (op : Op) -> Request op -> Type w

attribute [instance] Signature.opDecEq

/-- Stable nominal identity for a provider implementation. -/
structure ProviderId where
  domain : String
  name : String
  major : Nat
deriving BEq, DecidableEq, Repr

/-- An implementation of one operation in a dependent signature. -/
structure Provider (sig : Signature) (op : sig.Op) where
  id : ProviderId
  handle : (request : sig.Request op) -> Except String (sig.Response op request)

/-- A heterogeneous provider registry. -/
abbrev Registry (sig : Signature) := (op : sig.Op) -> Option (Provider sig op)

/-- A component's capability declaration. -/
abbrev Needs (sig : Signature) := sig.Op -> Prop

/-- Evidence that a particular provider is the committed binding for an operation. -/
structure Binding
    (sig : Signature)
    (registry : Registry sig)
    (op : sig.Op) where
  provider : Provider sig op
  present : registry op = some provider

/--
A committed capability view. The only way to obtain a binding is to provide a
proof that the operation was declared in `needs`.
-/
structure View
    (sig : Signature)
    (registry : Registry sig)
    (needs : Needs sig) where
  resolve : (op : sig.Op) -> needs op -> Binding sig registry op

namespace View

/-- Invoke a declared operation through its committed binding. -/
def call
    {sig : Signature}
    {registry : Registry sig}
    {needs : Needs sig}
    (view : View sig registry needs)
    (op : sig.Op)
    (declared : needs op)
    (request : sig.Request op) : Except String (sig.Response op request) :=
  (view.resolve op declared).provider.handle request

/-- The provider identity selected for a declared operation. -/
def providerId
    {sig : Signature}
    {registry : Registry sig}
    {needs : Needs sig}
    (view : View sig registry needs)
    (op : sig.Op)
    (declared : needs op) : ProviderId :=
  (view.resolve op declared).provider.id

/-- A committed view always resolves to a provider that is present in its registry. -/
theorem provider_present
    {sig : Signature}
    {registry : Registry sig}
    {needs : Needs sig}
    (view : View sig registry needs)
    (op : sig.Op)
    (declared : needs op) :
    registry op = some (view.resolve op declared).provider :=
  (view.resolve op declared).present

end View

/-- An existential request decoded from a dynamic boundary. -/
structure SomeCall (sig : Signature) where
  op : sig.Op
  request : sig.Request op

/-- A call paired with proof that its operation is in a component's capability set. -/
structure AuthorizedCall (sig : Signature) (needs : Needs sig) extends SomeCall sig where
  declared : needs op

/-- The response to an authorized call, indexed by that exact call. -/
structure Reply
    {sig : Signature}
    {needs : Needs sig}
    (call : AuthorizedCall sig needs) where
  value : sig.Response call.op call.request

namespace View

/-- Execute an authorized call while preserving the call/response dependency. -/
def execute
    {sig : Signature}
    {registry : Registry sig}
    {needs : Needs sig}
    (view : View sig registry needs)
    (call : AuthorizedCall sig needs) : Except String (Reply call) :=
  match view.call call.op call.declared call.request with
  | .ok response => .ok { value := response }
  | .error error => .error error

end View

/-- A component receives only its declared view and returns a pure result. -/
structure Component
    (sig : Signature)
    (registry : Registry sig)
    (needs : Needs sig) where
  Output : Type
  apply : View sig registry needs -> Output

end Cordis
