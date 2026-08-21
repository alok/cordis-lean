import Cordis.DeepSeekApi

/-!
# Process-backed DeepSeek HTTP transport

`DeepSeekApi` deliberately leaves HTTP as a `Transport` seam. This module supplies the first
runtime adapter for that seam: it invokes a configured process (normally `curl`), passes the
request body on standard input, passes headers as direct argv values rather than through a shell,
and asks the process to append a private status trailer. The response body and status are then
returned to the typed `DeepSeekApi.execute` decoder.

The adapter proves the argv/body/status protocol and exercises it with a deterministic `sh`
fixture. It does not prove that a network was reachable, a credential was valid, a remote service
answered honestly, or that an external process is trustworthy. Those remain explicit runtime
observations at the process boundary.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlTransport

open Cordis
open Cordis.DeepSeekApi

/-! ## Process output protocol -/

def statusMarker : String := "\n__CORDIS_HTTP_STATUS__"

inductive ProcessError where
  | spawn (message : String)
  | exited (code : UInt32) (stderr : String)
  | malformedOutput (output : String)
  | malformedStatus (suffix : String)
deriving DecidableEq, Repr

def ProcessError.message : ProcessError -> String
  | .spawn message => "process spawn failed: " ++ message
  | .exited code stderr =>
      "process exited with code " ++ toString code ++ "; stderr: " ++ stderr
  | .malformedOutput output => "missing or repeated status trailer in output: " ++ output
  | .malformedStatus suffix => "status trailer is not a decimal status: " ++ suffix

def parseOutput (output : String) : Except ProcessError HttpResponse :=
  match output.splitOn statusMarker with
  | [body, suffix] =>
      match suffix.trimAscii.toString.toNat? with
      | some status => .ok { status, body }
      | none => .error (.malformedStatus suffix)
  | _ => .error (.malformedOutput output)

theorem parseOutput_of_split
    {output body suffix : String} {status : Nat}
    (split : output.splitOn statusMarker = [body, suffix])
    (statusEq : suffix.trimAscii.copy.toNat? = some status) :
    parseOutput output = .ok { status, body } := by
  simp [parseOutput, split, statusEq]

/-! ## Direct process configuration -/

structure ProcessConfig where
  command : String
  args : HttpRequest -> Array String

def runProcess (config : ProcessConfig) (request : HttpRequest) :
    IO (Except ProcessError HttpResponse) := do
  try
    let output ← IO.Process.output {
      cmd := config.command
      args := config.args request
    } (some request.body)
    if output.exitCode == 0 then
      pure (parseOutput output.stdout)
    else
      pure (.error (.exited output.exitCode output.stderr))
  catch error =>
    pure (.error (.spawn (toString error)))

def processTransport (config : ProcessConfig) : Transport where
  send request := do
    match ← runProcess config request with
    | .ok response => pure (.ok response)
    | .error error => pure (.error error.message)

/-! ## Curl argv adapter -/

structure CurlConfig where
  executable : String := "curl"
  timeoutSeconds : Nat := 60
  extraArgs : Array String := #[]
deriving DecidableEq, Repr

private def methodText : HttpMethod -> String
  | .post => "POST"

private def addHeaders : List Header -> Array String -> Array String
  | [], args => args
  | header :: rest, args =>
      addHeaders rest ((args.push "--header").push (header.name ++ ": " ++ header.value))

def curlArgs (config : CurlConfig) (request : HttpRequest) : Array String :=
  let base := #[
    "--silent",
    "--show-error",
    "--request", methodText request.method,
    "--url", request.url,
    "--max-time", toString config.timeoutSeconds
  ]
  let withHeaders := addHeaders request.headers base
  withHeaders ++ config.extraArgs ++ #[
    "--data-binary", "@-",
    "--write-out", statusMarker ++ "%{http_code}\n"
  ]

def curlTransport (config : CurlConfig := {}) : Transport :=
  processTransport {
    command := config.executable
    args := curlArgs config
  }

/-! ## Deterministic process fixture -/

def fixtureProcess (responseBody : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-fixture",
    responseBody
  ]

def fixtureTransport (responseBody : String) : Transport :=
  processTransport (fixtureProcess responseBody)

def fixtureRequest : RequestPlan :=
  buildRequest "https://fixture.invalid" { value := "fixture-key" } exampleRequest

def fixtureResponse : IO (Except ClientError (Sigma fun body : String => ValidatedResponse body)) :=
  execute (fixtureTransport exampleResponseBody) fixtureRequest

end Cordis.DeepSeekCurlTransport
