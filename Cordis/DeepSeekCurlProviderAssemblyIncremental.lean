import Cordis.DeepSeekCurlIncremental
import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekProviderAssemblyPrefix
import Cordis.DeepSeekRichMultiStream
import Cordis.DeepSeekStreamIncremental

/-!
# Process-backed incremental provider assembly

This module closes the process/prefix/provider seam at line boundaries.  Every accepted body line
is parsed into the prefix wire certificate, projected through the multi-call rich state, mapped to
provider chunks, and folded into the source-shaped `BlockAssembler` state before the next process
read.  The terminal result retains all prefix snapshots and a final assembly certificate.

The adapter is intentionally not a live-provider theorem: reads are synchronous and
line-oriented, and blocked-read interruption, backpressure, reconnects, credentials, executable
trust, external effects, persistence, and deployed TypeScript equivalence remain external.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlProviderAssemblyIncremental

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderAssemblyPrefix
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekRichMultiStream
open Cordis.DeepSeekStream
open Cordis.DeepSeekStreamIncremental

inductive PrefixProviderError where
  | process (error : IncrementalError)
  | wire (error : StreamError)
  | projection (error : ProjectionError)
  | provider (error : ProviderStreamError)
  | assembly (error : AssemblyError)
  | callbackBodyMismatch (observed expected : String)
  | callbackCountMismatch (accepted observed : Nat)
  | callbackMissing
deriving DecidableEq, Repr

structure PrefixSnapshot where
  body : String
  frames : List Frame
  parsed : parseSsePrefix body = .ok frames
  multi : MultiState
  raw : List RichStream.RawChunk
  projection : projectFramesPrefix MultiState.initial frames = .ok (multi, raw)
  provider : Cordis.DeepSeekProviderAssemblyPrefix.PrefixState
  provider_eq : pushAll initial raw = .ok provider

def buildSnapshot (body : String) : Except PrefixProviderError PrefixSnapshot :=
  match parsed : parseSsePrefix body with
  | .error error => .error (.wire error)
  | .ok frames =>
      match projection : projectFramesPrefix MultiState.initial frames with
      | .error error => .error (.projection error)
      | .ok (multi, raw) =>
          match providerEq : pushAll initial raw with
          | .error error => .error (.provider error)
          | .ok provider => .ok {
              body
              frames
              parsed
              multi
              raw
              projection
              provider
              provider_eq := providerEq
            }

def finishSnapshot (snapshot : PrefixSnapshot) :
    Except AssemblyError (Certificate snapshot.provider.chunks) :=
  finish snapshot.provider

theorem buildSnapshot_body
    {body : String}
    {snapshot : PrefixSnapshot}
    (built : buildSnapshot body = .ok snapshot) :
    snapshot.body = body := by
  unfold buildSnapshot at built
  split at built <;> try contradiction
  split at built <;> try contradiction
  split at built <;> try contradiction
  cases built
  rfl

theorem finishSnapshot_exact
    {snapshot : PrefixSnapshot}
    {certificate : Certificate snapshot.provider.chunks}
    (finished : finishSnapshot snapshot = .ok certificate) :
    assemble snapshot.provider.state = .ok certificate.result := by
  exact DeepSeekProviderAssemblyPrefix.finish_exact finished

structure Processed (body : String) where
  observed : IncrementalResponse body
  accepted : List PrefixSnapshot
  last : PrefixSnapshot
  last_body : last.body = body ∨ last.body = body ++ "\n"
  final : PrefixSnapshot
  final_eq : final.body = body
  accepted_count_eq : accepted.length = observed.lines.length
  certificate : Certificate final.provider.chunks
  certificate_eq : finishSnapshot final = .ok certificate

private def rememberLine
    (bodyRef : IO.Ref String)
    (snapshotsRef : IO.Ref (List PrefixSnapshot))
    (errorRef : IO.Ref (Option PrefixProviderError))
    (_lineIndex : Nat)
    (line : String) : IO Unit := do
  let body ← bodyRef.get
  let nextBody := body ++ line
  bodyRef.set nextBody
  match ← errorRef.get with
  | some _ => pure ()
  | none =>
      match buildSnapshot nextBody with
      | .error error => errorRef.set (some error)
      | .ok snapshot => snapshotsRef.modify (fun snapshots => snapshots ++ [snapshot])

def execute
    (maxReads : Nat)
    (config : DeepSeekCurlTransport.ProcessConfig)
    (request : HttpRequest) :
    IO (Except PrefixProviderError (Sigma fun body : String => Processed body)) := do
  let bodyRef ← IO.mkRef ""
  let snapshotsRef ← IO.mkRef ([] : List PrefixSnapshot)
  let errorRef ← IO.mkRef (none : Option PrefixProviderError)
  let observed ← executeSseIncremental maxReads config request
    (rememberLine bodyRef snapshotsRef errorRef)
  match observed with
  | .error error => pure (.error (.process error))
  | .ok ⟨body, response⟩ =>
      match ← errorRef.get with
      | some error => pure (.error error)
      | none =>
          let accepted ← snapshotsRef.get
          match accepted.getLast? with
          | none => pure (.error .callbackMissing)
          | some last =>
              if bodyEq : last.body = body then
                match bodySnapshot : buildSnapshot body with
                | .error error => pure (.error error)
                | .ok final =>
                    have finalBody : final.body = body := buildSnapshot_body bodySnapshot
                    if countEq : accepted.length = response.lines.length then
                      match finished : finishSnapshot final with
                      | .error error => pure (.error (.assembly error))
                      | .ok certificate =>
                          pure (.ok ⟨body, {
                            observed := response
                            accepted
                            last
                            last_body := .inl bodyEq
                            final
                            final_eq := finalBody
                            accepted_count_eq := countEq
                            certificate
                            certificate_eq := finished
                          }⟩)
                      else
                        pure (.error
                          (.callbackCountMismatch accepted.length response.lines.length))
              else if paddingEq : last.body = body ++ "\n" then
                match bodySnapshot : buildSnapshot body with
                | .error error => pure (.error error)
                | .ok final =>
                    have finalBody : final.body = body := buildSnapshot_body bodySnapshot
                    if countEq : accepted.length = response.lines.length then
                      match finished : finishSnapshot final with
                      | .error error => pure (.error (.assembly error))
                      | .ok certificate =>
                          pure (.ok ⟨body, {
                            observed := response
                            accepted
                            last
                            last_body := .inr paddingEq
                            final
                            final_eq := finalBody
                            accepted_count_eq := countEq
                            certificate
                            certificate_eq := finished
                          }⟩)
                      else
                        pure (.error
                          (.callbackCountMismatch accepted.length response.lines.length))
              else
                pure (.error (.callbackBodyMismatch last.body body))

def counterProcess : DeepSeekCurlTransport.ProcessConfig :=
  DeepSeekCurlIncremental.fixtureProcess DeepSeekProviderStreamAssembly.counterBody

def counterRequest : HttpRequest := DeepSeekCurlTransport.fixtureRequest.request

def counterRun : IO (Except PrefixProviderError
    (Sigma fun body : String => Processed body)) :=
  execute 64 counterProcess counterRequest

def counterSummary : IO Bool := do
  match ← counterRun with
  | .error _ => pure false
  | .ok ⟨_, processed⟩ =>
      pure (processed.accepted.length == processed.observed.lines.length &&
        processed.accepted.length == 9 &&
        processed.final.frames.length == 4 &&
        processed.final.raw.length == 6 &&
        processed.certificate.result.blocks == [
          .toolCall "counter-call-0" "counter_increment" "[3,10]" ] &&
        processed.certificate.result.finish == .toolCalls)

end Cordis.DeepSeekCurlProviderAssemblyIncremental
