import Cordis.DeepSeekHarnessCompatibility
import Lean.Data.Json.FromToJson.Basic

/-! JSONL test driver for the shared semantic request corpus. -/

set_option autoImplicit false

namespace Integration.HarnessRequestDriver

open Lean Cordis.DeepSeekApi

structure CallInput where
  id : String
  name : String
  arguments : String
deriving FromJson

structure MessageInput where
  role : String
  content : Option String := none
  reasoning : Option String := none
  toolCalls : Option (List CallInput) := none
  toolCallId : Option String := none
deriving FromJson

structure ToolInput where
  name : String
  description : Option String := none
  parameters : Json
  strict : Option Bool := none
deriving FromJson

structure RequestInput where
  model : String
  messages : List MessageInput
  system : Option String := none
  tools : Option (List ToolInput) := none
  thinking : Option String := none
  reasoningEffort : Option String := none
  maxTokens : Option Nat := none
  responseFormat : Option String := none
  toolChoice : Option String := none
deriving FromJson

structure CaseInput where
  id : String
  request : RequestInput
deriving FromJson

def MessageInput.decode (message : MessageInput) : Except String ChatMessage := do
  match message.role with
  | "system" => .ok (.system (message.content.getD ""))
  | "user" => .ok (.user (message.content.getD ""))
  | "assistant" => .ok (.assistant message.content message.reasoning
      ((message.toolCalls.getD []).map fun call ↦ {
        id := call.id
        name := call.name
        arguments := call.arguments }))
  | "tool" =>
      let id ← match message.toolCallId with
        | some id => .ok id
        | none => .error "tool message requires toolCallId"
      .ok (.tool id (message.content.getD ""))
  | role => .error s!"unsupported role: {role}"

def RequestInput.decode (input : RequestInput) : Except String ChatRequest := do
  let converted ← input.messages.mapM MessageInput.decode
  let converted := match input.system with
    | none => converted
    | some system => .system system :: converted
  let messages ← match converted with
    | [] => .error "empty messages"
    | head :: tail => .ok { head, tail : MessageList ChatMessage }
  let thinking ← input.thinking.mapM fun value ↦ match value with
    | "enabled" => .ok ThinkingMode.enabled
    | "disabled" => .ok .disabled
    | _ => .error "unsupported thinking"
  let reasoningEffort ← input.reasoningEffort.mapM fun value ↦ match value with
    | "high" => .ok ReasoningEffort.high
    | "max" => .ok .max
    | _ => .error "unsupported reasoning effort"
  let responseFormat ← input.responseFormat.mapM fun value ↦ match value with
    | "text" => .ok ResponseFormat.text
    | "json_object" => .ok .jsonObject
    | _ => .error "unsupported response format"
  let toolChoice ← input.toolChoice.mapM fun value ↦ match value with
    | "none" => .ok ToolChoice.none
    | "auto" => .ok .auto
    | "required" => .ok .required
    | _ => .error "unsupported tool choice"
  return {
    model := input.model
    messages
    thinking
    reasoningEffort
    maxTokens := input.maxTokens
    responseFormat
    toolChoice
    tools := (input.tools.getD []).map fun tool ↦ { function := {
      name := tool.name
      description := tool.description
      parameters := tool.parameters
      strict := tool.strict } }
  }

def evaluate (input : CaseInput) : Json :=
  let result := do
    let request ← input.request.decode
    let plan ← Cordis.DeepSeekHarnessCompatibility.buildRequest
      "https://fixture.invalid" { value := "fixture-key" } request
    Json.parse plan.request.body
  .mkObj [("id", .str input.id), match result with
    | .ok body => ("ok", body)
    | .error error => ("error", .str error)]

end Integration.HarnessRequestDriver

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let input := Lean.Json.parse line >>=
      Lean.fromJson? (α := Integration.HarnessRequestDriver.CaseInput)
    match input with
    | .error error => throw (IO.userError error)
    | .ok value => stdout.putStrLn (Integration.HarnessRequestDriver.evaluate value).compress
