import Cordis.DurableBytes

/-!
# Stateful durable-byte adapters

`DurableSettlement`, `DurableCodec`, and `DurableBytes` prove the pure part of a
crash-prefix protocol.  This module is the next boundary: it gives that protocol a
small stateful backend interface, an actual filesystem implementation, and a mutable
in-memory implementation used by the executable tests.

The interface deliberately separates an operating-system acknowledgement from a
semantic certificate.  `appendPlan` returns `.ok plan` when the backend's write and
flush actions return; it does not pretend that this proves media durability.
`readAndRecover` turns the bytes actually returned by a backend into the existing
dependent scanner result.  A caller that wants a theorem about a particular expected
log must supply the equality in `RecoveryCertificate`; the equality is never inferred
from a string, file path, or successful system call.

The filesystem adapter therefore provides executable evidence for the boundary while
keeping fsync, crash atomicity, multi-process locking, checksums, and external tool
effects explicit.  The pure theorems below still establish exact restart recovery once
the returned scan is related to the expected typed log.
-/

namespace Cordis.DurableIO

open Cordis
open Cordis.DurableCodec
open Cordis.DurableBytes
open Cordis.DurableSettlement

universe u v

set_option autoImplicit false

abbrev Bytes := List UInt8

/-! ## Backend and byte conversion -/

/-- Convert the pure byte list used by the proof layer to Lean's binary buffer. -/
def toByteArray (bytes : Bytes) : ByteArray := ByteArray.mk bytes.toArray

/-- A backend supplies reads and append/replace operations with an explicit flush. -/
structure Backend where
  read : IO Bytes
  appendFlush : Bytes → IO Unit
  replaceFlush : Bytes → IO Unit

/-- A filesystem-backed implementation of the backend contract. -/
structure FileBackend where
  path : System.FilePath

namespace FileBackend

/-- Construct a backend for an existing or creatable path. -/
def backend (file : FileBackend) : Backend where
  read := do
    let bytes ← IO.FS.readBinFile file.path
    pure bytes.toList
  appendFlush := fun bytes =>
    IO.FS.withFile file.path IO.FS.Mode.append fun handle => do
      handle.write (toByteArray bytes)
      handle.flush
  replaceFlush := fun bytes =>
    IO.FS.withFile file.path IO.FS.Mode.write fun handle => do
      handle.write (toByteArray bytes)
      handle.flush

end FileBackend

/-- An executable mutable backend for tests and deterministic adapter examples. -/
structure MemoryStore where
  contents : IO.Ref Bytes

namespace MemoryStore

/-- Allocate a memory backend with the supplied initial byte sequence. -/
def new (initial : Bytes := []) : IO MemoryStore := do
  return { contents := ← IO.mkRef initial }

/-- Read the current bytes from the memory store. -/
def read (store : MemoryStore) : IO Bytes :=
  ST.Ref.get store.contents

/-- Return the backend view of a memory store. -/
def backend (store : MemoryStore) : Backend where
  read := read store
  appendFlush := fun bytes => ST.Ref.modify store.contents (fun current ↦ current ++ bytes)
  replaceFlush := fun bytes => ST.Ref.set store.contents bytes

end MemoryStore

/-! ## Typed append plans and operational outcomes -/

/-- The exact frame and bytes that a typed log append is expected to emit. -/
structure AppendPlan
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry)
    (codec : PayloadCodec RawFrame)
    (initial : State)
    {current : State} {nextSequence : Nat} {digest : Digest}
    (log : Log wire.spec initial current nextSequence digest)
    (entry : Entry) where
  raw : RawFrame
  raw_eq : raw = RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec digest nextSequence entry current)
  bytes : Bytes
  bytes_eq : bytes = encodeFrame codec raw

namespace AppendPlan

variable {State : Type u} {Entry : Type v}
variable {wire : WireSpec State Entry} {codec : PayloadCodec RawFrame}
variable {initial : State} {current : State} {nextSequence : Nat} {digest : Digest}
variable {log : Log wire.spec initial current nextSequence digest} {entry : Entry}

/-- The canonical plan emitted by the indexed settlement log. -/
def canonical (log : Log wire.spec initial current nextSequence digest) (entry : Entry) :
    AppendPlan wire codec initial log entry where
  raw := RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec digest nextSequence entry current)
  raw_eq := rfl
  bytes := encodeFrame codec (RawFrame.ofFrame wire.spec
    (Frame.expected wire.spec digest nextSequence entry current))
  bytes_eq := rfl

/-- The exact typed successor represented by the plan. -/
def nextLog (_plan : AppendPlan wire codec initial log entry) :
    Log wire.spec initial
      (wire.spec.after entry current)
      (nextSequence + 1)
      (wire.spec.frameDigest digest nextSequence entry
        (wire.spec.stateCode (wire.spec.after entry current))) :=
  .append log entry

/-- The binary codec accepts the planned frame and leaves no suffix. -/
theorem decode_bytes (plan : AppendPlan wire codec initial log entry) :
    decodeFrame codec plan.bytes = .ok (plan.raw, []) := by
  rw [plan.bytes_eq]
  simpa using decodeFrame_encode codec plan.raw []

/-- The planned raw frame is the unique expected frame for the indexed append. -/
theorem raw_is_expected (plan : AppendPlan wire codec initial log entry) :
    plan.raw = RawFrame.ofFrame wire.spec
      (Frame.expected wire.spec digest nextSequence entry current) :=
  plan.raw_eq

end AppendPlan

/-- Run a planned append, preserving the distinction between acknowledgement and failure. -/
def appendPlan
    {State : Type} {Entry : Type}
    {wire : WireSpec State Entry} {codec : PayloadCodec RawFrame}
    {initial : State} {current : State} {nextSequence : Nat} {digest : Digest}
    {log : Log wire.spec initial current nextSequence digest} {entry : Entry}
    (backend : Backend) (plan : AppendPlan wire codec initial log entry) :
    IO (Except String (AppendPlan wire codec initial log entry)) := do
  try
    backend.appendFlush plan.bytes
    pure (.ok plan)
  catch error =>
    pure (.error error.toString)

/-! ## Reading, scanning, and typed restart certificates -/

/-- Read failure is kept separate from a valid byte sequence rejected by the scanner. -/
abbrev ReadScanError := String ⊕ ScanBytesError

/-- Read bytes and scan an explicitly supplied crash-prefix frame count. -/
def readAndRecover
    {State : Type} {Entry : Type}
    (backend : Backend)
    (wire : WireSpec State Entry) (initial : State)
    (codec : PayloadCodec RawFrame) (count : Nat) :
    IO (Except ReadScanError
      (@Cordis.DurableCodec.ScannedLog State Entry wire initial × Bytes)) := do
  try
    let bytes ← backend.read
    pure ((scanBytesPrefix wire initial codec count bytes).mapError Sum.inr)
  catch error =>
    pure (.error (.inl error.toString))

/-- A successful scan plus its unconsumed bytes is the restart certificate. -/
structure RecoveryCertificate
    {State : Type u} {Entry : Type v}
    (wire : WireSpec State Entry) (initial : State) where
  value : @Cordis.DurableCodec.ScannedLog State Entry wire initial
  suffix : Bytes

namespace RecoveryCertificate

variable {State : Type u} {Entry : Type v}
variable {wire : WireSpec State Entry} {initial : State}
variable (certificate : RecoveryCertificate wire initial)

/-- The expected-log relation is deliberately heterogeneous because the scan carries indices. -/
def MatchesExpected
    {current : State} {nextSequence : Nat} {digest : Digest}
    (expected : Log wire.spec initial current nextSequence digest) : Prop :=
  HEq certificate.value.log expected

/-- The scanned prefix recovers the initial model exactly. -/
theorem recovers_initial
    :
    certificate.value.log.accumulatedUndo wire.spec initial certificate.value.current = initial :=
  certificate.value.log.recovers

/-- The discarded suffix is observationally retained rather than silently parsed. -/
theorem discarded_is_explicit
    :
    ∃ suffix, suffix = certificate.suffix :=
  ⟨certificate.suffix, rfl⟩

end RecoveryCertificate

/-- Convert one scanned result into a recovery certificate when its endpoint is known. -/
def certifyRecovery
    {State : Type u} {Entry : Type v}
    {wire : WireSpec State Entry} {initial : State}
    (scanned : @Cordis.DurableCodec.ScannedLog State Entry wire initial)
    (discarded : Bytes) :
    RecoveryCertificate wire initial :=
  { value := scanned, suffix := discarded }

/-! ## Executable examples -/

namespace Example

open Cordis.DurableCodec.Example

def firstPlan : AppendPlan wire rawFramePayloadCodec DurableSettlement.Example.initial
    (.empty : Log wire.spec DurableSettlement.Example.initial DurableSettlement.Example.initial 0
      (DurableSettlement.Spec.genesisDigest DurableSettlement.Example.spec)) 3 :=
  AppendPlan.canonical .empty 3

theorem firstPlan_decodes :
    decodeFrame rawFramePayloadCodec firstPlan.bytes = Except.ok (firstPlan.raw, []) := by
  exact AppendPlan.decode_bytes firstPlan

theorem firstPlan_next_is_first :
    firstPlan.nextLog = DurableSettlement.Example.first := by
  rfl

def memoryResume : IO Bool := do
  let store ← MemoryStore.new
  let backend := store.backend
  let firstAppend ← appendPlan backend firstPlan
  match firstAppend with
  | .error _ => pure false
  | .ok _ =>
      let recovered ← readAndRecover backend wire DurableSettlement.Example.initial
        rawFramePayloadCodec 1
      match recovered with
      | .error _ => pure false
      | .ok (scanned, discarded) =>
          let second := AppendPlan.canonical (wire := wire)
            (codec := rawFramePayloadCodec) scanned.log 8
          let secondAppend ← appendPlan backend second
          match secondAppend with
          | .error _ => pure false
          | .ok _ =>
              let final ← readAndRecover backend wire DurableSettlement.Example.initial
                rawFramePayloadCodec 2
              match final with
              | .error _ => pure false
              | .ok (scannedFinal, suffix) =>
                  pure (scanned.current = 13 ∧ discarded = [] ∧
                    scannedFinal.current = 21 ∧ suffix = [])

def memoryTornPrefix : IO Bool := do
  let store ← MemoryStore.new
  let backend := store.backend
  let firstAppend ← appendPlan backend firstPlan
  match firstAppend with
  | .error _ => pure false
  | .ok _ =>
      backend.appendFlush [0]
      let recovered ← readAndRecover backend wire DurableSettlement.Example.initial
        rawFramePayloadCodec 1
      match recovered with
      | .error _ => pure false
      | .ok (scanned, discarded) =>
          pure (scanned.current = 13 ∧ discarded = [0])

def fileResume : IO Bool :=
  IO.FS.withTempFile fun _ path => do
    let backend := (FileBackend.mk path).backend
    let firstAppend ← appendPlan backend firstPlan
    match firstAppend with
    | .error _ => pure false
    | .ok _ =>
        let recovered ← readAndRecover backend wire DurableSettlement.Example.initial
          rawFramePayloadCodec 1
        match recovered with
        | .error _ => pure false
        | .ok (scanned, discarded) =>
            let second := AppendPlan.canonical (wire := wire)
              (codec := rawFramePayloadCodec) scanned.log 8
            let secondAppend ← appendPlan backend second
            match secondAppend with
            | .error _ => pure false
            | .ok _ =>
                let final ← readAndRecover backend wire DurableSettlement.Example.initial
                  rawFramePayloadCodec 2
                match final with
                | .error _ => pure false
                | .ok (scannedFinal, suffix) =>
                    pure (scanned.current = 13 ∧ discarded = [] ∧
                      scannedFinal.current = 21 ∧ suffix = [])

end Example

end Cordis.DurableIO
