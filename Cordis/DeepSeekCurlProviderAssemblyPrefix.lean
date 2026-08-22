import Cordis.DeepSeekCurlPrefix
import Cordis.DeepSeekProviderStreamAssembly

/-!
# Process-backed prefix to provider assembly

This module composes the line-oriented process prefix with the source-shaped provider assembler.
The process prefix retains every accepted line and its strict SSE completion certificate; only a
completed prefix is then passed to the whole-body rich/provider validator, which retains the exact
provider chunk fold and terminal assembly.  This makes the terminal seam explicit without claiming
that provider assembly is incremental or that the deployed TypeScript reader is equivalent.

Fuel exhaustion and line cancellation remain typed prefix outcomes.  Network reachability,
credentials, process trust, backpressure, blocked-read cancellation, persistence, external effects,
and deployed Harness equivalence remain outside this module.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlProviderAssemblyPrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekStreamIncremental

inductive PrefixAssemblyError where
  | client (error : PrefixClientError)
  | provider (error : ProviderStreamError)
  | fuelExhausted
  | cancelled (line : Nat) (reason : String)
deriving DecidableEq, Repr

structure ProcessedProviderPrefix (policy : LinePolicy) where
  observed : PrefixResponse policy
  provider : ValidatedProviderAssembly observed.state.body
  provider_eq : validateBody observed.state.body = .ok provider

private def requireCompleted
    {policy : LinePolicy}
    (response : PrefixResponse policy) :
    Except PrefixAssemblyError (ProcessedProviderPrefix policy) :=
  match response.stop with
  | .completed _ =>
      match validated : validateBody response.state.body with
      | .error error => .error (.provider error)
      | .ok provider => .ok { observed := response, provider, provider_eq := validated }
  | .fuelExhausted => .error .fuelExhausted
  | .cancelled line reason _ => .error (.cancelled line reason)

def executeWith
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (Except PrefixAssemblyError (ProcessedProviderPrefix policy)) := do
  match ← executeSsePrefix policy maxReads config request with
  | .error error => pure (.error (.client error))
  | .ok response => pure (requireCompleted response)

theorem ProcessedProviderPrefix.source_exact
    {policy : LinePolicy}
    (processed : ProcessedProviderPrefix policy) :
    validateBody processed.observed.state.body = .ok processed.provider :=
  processed.provider_eq

theorem ProcessedProviderPrefix.assembly_exact
    {policy : LinePolicy}
    (processed : ProcessedProviderPrefix policy) :
    assemble processed.provider.assembly.state = .ok processed.provider.assembly.result :=
  processed.provider.assembly.result_eq

def counterProcess : ProcessConfig :=
  DeepSeekCurlIncremental.fixtureProcess DeepSeekProviderStreamAssembly.counterBody

def counterRequest : HttpRequest :=
  DeepSeekCurlTransport.fixtureRequest.request

def counterRun : IO (Except PrefixAssemblyError
    (ProcessedProviderPrefix (LinePolicy.never))) :=
  executeWith (LinePolicy.never) 64 counterProcess counterRequest

def counterSummary : IO Bool := do
  match ← counterRun with
  | .error _ => pure false
  | .ok processed =>
      pure (processed.observed.state.line == 9 &&
        processed.provider.source.wire.frames.length == 4 &&
        processed.provider.assembly.result.blocks == [
          .toolCall "counter-call-0" "counter_increment" "[3,10]" ] &&
        processed.provider.assembly.result.finish == .toolCalls)

end Cordis.DeepSeekCurlProviderAssemblyPrefix
