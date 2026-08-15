import Cordis

def main : IO Unit := do
  if Cordis.version == "0.1.0" then
    IO.println "CORDIS Lean scaffold test passed"
  else
    throw <| IO.userError "unexpected CORDIS Lean version"
