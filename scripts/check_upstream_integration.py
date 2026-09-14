#!/usr/bin/env python3
"""Compare complete request JSON against the actual, pinned Harness serializer."""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
Json = Any


def run(args: list[str], *, cwd: Path = ROOT, input_text: str | None = None) -> str:
    result = subprocess.run(args, cwd=cwd, input=input_text, text=True,
                            capture_output=True, timeout=240)
    if result.returncode:
        raise RuntimeError(f"{args!r} failed ({result.returncode}):\n"
                           f"{result.stdout}\n{result.stderr}")
    return result.stdout


def prepare_upstream(path: Path, pin: dict[str, str]) -> None:
    if not path.exists():
        path.mkdir(parents=True)
        run(["git", "init", str(path)])
        run(["git", "remote", "add", "origin", pin["repository"]], cwd=path)
        run(["git", "fetch", "--depth=1", "origin", pin["revision"]], cwd=path)
        run(["git", "switch", "--detach", pin["revision"]], cwd=path)
    actual = run(["git", "rev-parse", "HEAD"], cwd=path).strip()
    if actual != pin["revision"]:
        raise RuntimeError(f"Upstream revision {actual} does not match {pin['revision']}")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=path).strip():
        raise RuntimeError("Upstream checkout is dirty; refusing unpinned source")


def corpus() -> list[dict[str, Json]]:
    """Named boundaries plus a reproducible cross-product and generated histories."""
    cases: list[dict[str, Json]] = []

    def add(name: str, messages: list[dict[str, Json]], **options: Json) -> None:
        cases.append({"id": name, "request": {"model": "fixture-model",
                      "messages": messages, **options}})

    user = {"role": "user", "content": "hello"}
    call = {"id": "call-0", "name": "read", "arguments": "{}"}
    tool = {"name": "read", "description": "Read a value", "parameters": {
        "type": "object", "properties": {"key": {"type": "string"}}, "required": ["key"]}}
    add("plain", [user])
    add("empty-user", [{"role": "user", "content": ""}])
    add("system-only", [], system="Only a system prompt")
    add("empty-system", [user], system="")
    add("system-in-history", [{"role": "system", "content": "history"}, user], system="first")
    add("tool-without-description", [user], tools=[{"name": "f", "parameters": {}}])
    add("empty-tools", [user], tools=[])
    for text, reasoning, calls in itertools.product(
            [None, "", "answer\n雪🙂"], [None, "", "reasoning\nλ"], [[], [call]]):
        add(f"assistant-{len(cases):03}", [user, {"role": "assistant", "content": text,
            "reasoning": reasoning, "toolCalls": calls}])
    for thinking, effort, budget in itertools.product(
            [None, "enabled", "disabled"], [None, "high", "max"], [None, 0, 4096]):
        if thinking == "disabled" and effort is not None:
            continue
        options = {key: value for key, value in
                   [("thinking", thinking), ("reasoningEffort", effort), ("maxTokens", budget)]
                   if value is not None}
        add(f"options-{len(cases):03}", [user], **options)
    for output in ["", " ", "0", "\"quoted\"\n雪🙂"]:
        add(f"tool-result-{len(cases):03}", [user,
            {"role": "assistant", "toolCalls": [call]},
            {"role": "tool", "toolCallId": call["id"], "content": output}], tools=[tool])

    rng = random.Random(914)
    for index in range(64):
        count = rng.randint(1, 4)
        calls = [{"id": f"call-{index}-{n}", "name": f"tool-{n}",
                  "arguments": json.dumps({"n": n, "text": "λ\n\"🙂"}, ensure_ascii=False)}
                 for n in range(count)]
        tools = [{"name": item["name"], "description": "" if n % 2 else "schema 雪",
                  "parameters": {"type": "object", "properties": {
                      "n": {"type": "integer", "minimum": -n},
                      "text": {"type": "string", "enum": ["", "λ", "雪"]}},
                      "required": ["n"], "additionalProperties": False,
                      "x-fixture": {"index": index, "values": [None, True, 1.25]}}}
                 for n, item in enumerate(calls)]
        history = [user, {"role": "assistant", "content": rng.choice([None, "", "working"]),
                          "reasoning": rng.choice([None, "", "checking"]), "toolCalls": calls}]
        history += [{"role": "tool", "toolCallId": item["id"],
                     "content": rng.choice(["", "result", "0", "雪\n🙂"])} for item in calls]
        history.append({"role": "assistant", "content": "done", "reasoning": "drop me"})
        add(f"history-{index:03}", history, tools=tools, system=f"fixture {index}")
    return cases


def read_results(text: str) -> dict[str, Json]:
    rows: dict[str, Json] = {}
    for line in text.splitlines():
        row = json.loads(line)
        key = row["id"]
        if key in rows:
            raise ValueError(f"Duplicate case id: {key}")
        rows[key] = row
    return rows


def compare(expected: dict[str, Json], actual: dict[str, Json]) -> None:
    if not expected or expected.keys() != actual.keys():
        raise ValueError(f"Case set mismatch: missing={expected.keys() - actual.keys()}, "
                         f"extra={actual.keys() - expected.keys()}")
    for key in expected:
        # Canonical objects only; array order and JSON type distinctions stay observable.
        encode = lambda value: json.dumps(value, sort_keys=True, ensure_ascii=False)
        if encode(expected[key]) != encode(actual[key]):
            raise ValueError(f"Request mismatch in {key}:\n"
                             f"upstream: {encode(expected[key])}\nLean: {encode(actual[key])}")


def check_negative_controls(reference: dict[str, Json]) -> int:
    mutations = []
    changed = copy.deepcopy(reference)
    changed["plain"]["ok"].pop("stream_options")
    mutations.append(changed)
    changed = copy.deepcopy(reference)
    changed["plain"]["ok"]["stream"] = 1  # bool and int must not compare equal
    mutations.append(changed)
    changed = copy.deepcopy(reference)
    changed["history-000"]["ok"]["messages"].reverse()
    mutations.append(changed)
    changed = copy.deepcopy(reference)
    changed["history-000"]["ok"]["tools"][0]["function"]["parameters"] = {}
    mutations.append(changed)
    changed = copy.deepcopy(reference)
    del changed["plain"]
    mutations.append(changed)
    for changed in mutations:
        try:
            compare(reference, changed)
        except ValueError:
            continue
        raise AssertionError("Comparator accepted deliberately corrupted output")
    try:
        read_results('{"id":"duplicate"}\n{"id":"duplicate"}\n')
    except ValueError:
        return len(mutations) + 1
    raise AssertionError("Comparator accepted duplicate output")


def jsonl(rows: list[dict[str, Json]]) -> str:
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows)


def check_rejections(executable: Path) -> int:
    base = {"model": "fixture", "messages": [{"role": "user", "content": "hi"}]}
    unsupported = [
        {"responseFormat": "json_object"}, {"toolChoice": "required"},
        {"thinking": "disabled", "reasoningEffort": "high"},
        {"tools": [{"name": "strict", "parameters": {}, "strict": True}]},
        {"tools": [{"name": "strict", "parameters": {}, "strict": False}]},
    ]
    rows = [{"id": f"unsupported-{n}", "request": {**base, **fields}}
            for n, fields in enumerate(unsupported)]
    results = read_results(run([str(executable)], input_text=jsonl(rows)))
    expected = {row["id"]: {"id": row["id"],
                "error": "unsupported Harness compatibility request"} for row in rows}
    compare(expected, results)
    return len(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".lake/upstream/deepseek-harness")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/integration")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Invalidate any old success receipt before preflight, builds, or comparisons.
    receipt = output / "receipt.json"
    receipt.unlink(missing_ok=True)
    pin = json.loads((ROOT / "Integration/upstream.json").read_text())
    upstream = args.upstream.resolve()
    prepare_upstream(upstream, pin)
    version = run(["bun", "--version"]).strip()
    if version != pin["bun_version"]:
        raise RuntimeError(f"Expected Bun {pin['bun_version']}, found {version}")
    print("Building the Lean request driver", flush=True)
    run(["lake", "--wfail", "build", "cordis_upstream_request"])
    executable = ROOT / ".lake/build/bin/cordis_upstream_request"
    cases = corpus()
    data = jsonl(cases)
    corpus_path = output / "requests.jsonl"
    corpus_path.write_text(data)
    expected_text = run(["bun", str(ROOT / "Integration/upstream-request.ts"),
                         str(upstream), str(corpus_path)])
    (output / "upstream.jsonl").write_text(expected_text)
    actual_text = run([str(executable)], input_text=data)
    (output / "lean.jsonl").write_text(actual_text)
    expected, actual = read_results(expected_text), read_results(actual_text)
    if set(expected) != {row["id"] for row in cases}:
        raise ValueError("Upstream output does not cover the input corpus")
    compare(expected, actual)
    controls = check_negative_controls(expected)
    rejections = check_rejections(executable)
    report = {"upstream_revision": pin["revision"], "bun_version": version,
              "lean_revision": run(["git", "rev-parse", "HEAD"]).strip(),
              "lean_dirty": bool(run(["git", "status", "--porcelain"]).strip()),
              "corpus_sha256": hashlib.sha256(data.encode()).hexdigest(),
              "serializer_sha256": hashlib.sha256((upstream / pin["serializer"]).read_bytes()).hexdigest(),
              "matching_requests": len(cases), "negative_controls": controls,
              "unsupported_rejections": rejections}
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(cases)} exact requests, {controls} comparator controls, "
          f"{rejections} unsupported-field rejections. Receipt: {receipt}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
