import Cordis.Harness
import Cordis.Version

def main : IO Unit := do
  match Cordis.Harness.demo with
  | .error error =>
      throw <| IO.userError s!"CORDIS Lean demo failed: {repr error}"
  | .ok state =>
      IO.println s!"CORDIS Lean {Cordis.version} proof-carrying harness"
      IO.println s!"final modeled counter: {state.model}"
      IO.println s!"final protocol state: {repr state.protocol}"
      IO.println s!"replay-certified events: {state.log.length}"
      for record in state.records do
        let payload := if record.encodedResult.isSome then "encoded-result" else "no-result"
        IO.println (s!"call {record.id.value} {record.name}: {repr record.outcome}; " ++
          s!"policy-dispatches={record.policyDispatchCount}; {payload}")
