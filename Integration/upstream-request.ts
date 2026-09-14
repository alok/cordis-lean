import { plugin } from "bun";
import { resolve } from "node:path";

// Resolve the real pinned workspace modules; no serializer or error-class mocks.
const [upstream, corpus] = process.argv.slice(2);
if (!upstream || !corpus) throw new Error("usage: upstream-request.ts CHECKOUT CORPUS.jsonl");
const modules: Record<string, string> = {
  "@deepseek-ai/dsh-llm": "packages/llm/llm/src/index.ts",
  "@deepseek-ai/cordis": "vendor/cordis/src/index.ts",
  "@deepseek-ai/cosmokit": "vendor/cosmokit/src/index.ts",
  "@deepseek-ai/schemastery": "vendor/schemastery/src/index.ts",
  "@deepseek-ai/dsh-timeout": "packages/util/timeout/src/index.ts",
};
plugin({
  name: "pinned-harness-workspace",
  setup(build) {
    build.onResolve({ filter: /^@deepseek-ai\// }, ({ path }) => {
      if (!modules[path]) throw new Error(`Unmapped upstream dependency: ${path}`);
      return { path: resolve(upstream, modules[path]) };
    });
  },
});
const { serializeRequest } = await import(
  resolve(upstream, "packages/llm/llm-deepseek/src/serialize.ts")
);

type Call = { id: string; name: string; arguments: string };
type Message = {
  role: string; content?: string | null; reasoning?: string | null;
  toolCalls?: Call[]; toolCallId?: string;
};
type Request = {
  model: string; messages: Message[]; system?: string;
  tools?: { name: string; description?: string; parameters: unknown }[];
  thinking?: string; reasoningEffort?: string; maxTokens?: number;
};
function message(input: Message) {
  if (input.role === "tool") return {
    role: "user",
    content: [{ type: "tool-result", toolCallId: input.toolCallId,
      content: [{ type: "text", text: input.content ?? "" }] }],
  };
  const content: Record<string, unknown>[] = [{ type: "text", text: input.content ?? "" }];
  if (input.role === "assistant") {
    if (input.reasoning != null) content.push({ type: "reasoning", text: input.reasoning });
    for (const call of input.toolCalls ?? []) content.push({ type: "tool-call", ...call });
  }
  return { role: input.role, content };
}
for (const line of (await Bun.file(corpus).text()).trim().split("\n")) {
  const { id, request }: { id: string; request: Request } = JSON.parse(line);
  const options = { model: request.model, messages: request.messages.map(message),
    system: request.system, tools: request.tools, reasoningEffort: request.reasoningEffort,
    maxTokens: request.maxTokens };
  // JSON.stringify removes undefined exactly as the actual HTTP adapter does.
  const body = serializeRequest(options, { thinking: request.thinking });
  console.log(JSON.stringify({ id, ok: body }));
}
