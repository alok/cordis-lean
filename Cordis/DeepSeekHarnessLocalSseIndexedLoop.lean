import Cordis.DeepSeekHarnessLocalSseIndexed

/-!
# Two-round indexed loopback SSE conversation

`DeepSeekHarnessLocalSseIndexed` proves one real loopback SSE response can be admitted and
appended to an `ExtensionRunner`.  This module closes the next dependent seam: after the first
append, it reconstructs a fresh `Session.ModelRequest` from the resulting session, prepares that
request with the same source/header certificate, and runs a second real curl/loopback round.

The result keeps both indexed append witnesses and the second request's dependent type.  The
final sequence equation is therefore derived from the two append contracts rather than from a
counter in the executable fixture.  Each round is still a local one-shot HTTP fixture; remote
reachability, credentials, provider authenticity, persistence, reconnects, blocked-read
interruption, and deployed Harness equivalence remain outside this module.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseIndexedLoop

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekHarnessLocalSseIndexed
open Cordis.DeepSeekSessionRequest

inductive IndexedLoopError where
  | first (error : IndexedLocalSseError)
  | secondRequest (error : RequestError)
  | second (error : IndexedLocalSseError)
deriving DecidableEq, Repr

namespace Example

def initialHeader : Session.RequestHeader where
  provider := "deepseek"
  model := "deterministic-counter"
  system := none
  toolSchemas := []

def initialSession : Session.Session Session.noExtensions :=
  let empty := Session.Session.empty Session.noExtensions
  let headed := empty.appendLogOnly .requestHeader initialHeader
  headed.appendSurface .userMessage { content := "stream me twice" } [] (by simp) (by simp)

def initialRunner : ExtensionRunner Session.noExtensions where
  session := initialSession
  turn := 1
  step := initialSession.nextSeq
  nextCall := 0
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := by rfl

def encoder : ToolSchemaEncoder where
  encode schema := {
    function := {
      name := schema.name
      description := some schema.description
      parameters := .str schema.inputSchema
      strict := none
    }
  }
  name_eq _schema := rfl
  description_eq _schema := rfl

def request : Session.ModelRequest initialRunner.session :=
  match h : Session.mkRequest initialRunner.session with
  | none => nomatch h
  | some request => request

def source : RequestSource := sourceFor request encoder {}

def prepared : PreparedRequest request source encoder :=
  match h : prepare request source encoder (sourceFor_agreement request encoder {}) with
  | .error _error => nomatch h
  | .ok prepared => prepared

def body : String := DeepSeekRichStream.exampleTextStreamBody

/-! The second request is constructed from the exact first endpoint, not from a copied session. -/

def prepareNext
    (runner : ExtensionRunner Session.noExtensions) :
    Except RequestError
      (Sigma fun request : Session.ModelRequest runner.session =>
        PreparedRequest request (sourceFor request encoder {}) encoder) :=
  match _h : Session.mkRequest runner.session with
  | none => .error .emptyMessages
  | some request =>
      match _built : prepare request (sourceFor request encoder {}) encoder
          (sourceFor_agreement request encoder {}) with
      | .error error => .error error
      | .ok prepared => .ok ⟨request, prepared⟩

structure TwoRoundResult where
  first : IndexedLocalSseResult (runner := initialRunner) prepared
  secondRequest : Session.ModelRequest first.after.session
  secondPrepared :
    PreparedRequest secondRequest (sourceFor secondRequest encoder {}) encoder
  second : IndexedLocalSseResult (runner := first.after) secondPrepared

def run : IO (Except IndexedLoopError TwoRoundResult) := do
  match ← DeepSeekHarnessLocalSseIndexed.runWithKey (runner := initialRunner) prepared
      { value := "fixture-key" } body with
  | .error error => pure (.error (.first error))
  | .ok first =>
      match prepareNext first.after with
      | .error error => pure (.error (.secondRequest error))
      | .ok ⟨secondRequest, secondPrepared⟩ =>
          match ← DeepSeekHarnessLocalSseIndexed.runWithKey (runner := first.after)
              secondPrepared { value := "fixture-key" } body with
          | .error error => pure (.error (.second error))
          | .ok second =>
              pure (.ok {
                first
                secondRequest
                secondPrepared
                second
              })

theorem second_endpoint_exact (result : TwoRoundResult) :
    result.second.after = ExtensionRunner.appendFinished result.first.after
      result.second.localResult.finished [] (by simp) (by simp) :=
  result.second.append_eq

theorem second_nextSeq (result : TwoRoundResult) :
    result.second.after.session.nextSeq = result.first.after.session.nextSeq + 1 := by
  rw [result.second.append_eq]
  exact ExtensionRunner.appendFinished_nextSeq result.first.after
    result.second.localResult.finished [] (by simp) (by simp)

theorem final_nextSeq (result : TwoRoundResult) :
    result.second.after.session.nextSeq = initialRunner.session.nextSeq + 2 := by
  calc
    result.second.after.session.nextSeq = result.first.after.session.nextSeq + 1 :=
      second_nextSeq result
    _ = (initialRunner.session.nextSeq + 1) + 1 := by
      rw [result.first.append_eq]
      rw [ExtensionRunner.appendFinished_nextSeq]
    _ = initialRunner.session.nextSeq + 2 := by omega

structure Summary where
  firstRequests : Nat
  secondRequests : Nat
  firstValidRequests : Nat
  secondValidRequests : Nat
  firstFrames : Nat
  secondFrames : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
deriving BEq, DecidableEq, Repr

def summarize (result : TwoRoundResult) : Summary := {
  firstRequests := result.first.localResult.requests
  secondRequests := result.second.localResult.requests
  firstValidRequests := result.first.localResult.validRequests
  secondValidRequests := result.second.localResult.validRequests
  firstFrames := result.first.localResult.response.wire.frames.length
  secondFrames := result.second.localResult.response.wire.frames.length
  initialNextSeq := initialRunner.session.nextSeq
  finalNextSeq := result.second.after.session.nextSeq
}

def expectedSummary : Summary := {
  firstRequests := 1
  secondRequests := 1
  firstValidRequests := 1
  secondValidRequests := 1
  firstFrames := 3
  secondFrames := 3
  initialNextSeq := 2
  finalNextSeq := 4
}

theorem summary_initial_nextSeq (result : TwoRoundResult) :
    (summarize result).initialNextSeq = initialRunner.session.nextSeq := rfl

theorem summary_final_nextSeq (result : TwoRoundResult) :
    (summarize result).finalNextSeq = initialRunner.session.nextSeq + 2 :=
  final_nextSeq result

end Example

end Cordis.DeepSeekHarnessLocalSseIndexedLoop
