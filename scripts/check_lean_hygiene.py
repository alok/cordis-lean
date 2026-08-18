#!/usr/bin/env python3
"""Reject trust-broadening Lean source and nonstandard axiom dependencies."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Sequence


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SKIP_DIRECTORIES = frozenset({".git", ".lake"})
TOKEN = re.compile(r"(?:[^\W\d]|_)(?:\w|')*|[.#]")
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
AXIOM_LINE = re.compile(
    r"^'[^']+' (?:does not depend on any axioms|depends on axioms: \[(?P<axioms>.*)\])$"
)
FORBIDDEN = {
    "sorry": "proof placeholder",
    "sorryAx": "direct use of Lean's sorry axiom",
    "ofReduceBool": "compiler-trusting proof axiom",
    "trustCompiler": "compiler-trust axiom",
    "admit": "proof-admission tactic",
    "axiom": "project-defined axiom declaration",
    "axioms": "project-defined axiom declarations",
    "constant": "bodyless constant declaration",
    "constants": "bodyless constant declarations",
    "unsafe": "unsafe declaration or command",
    "partial": "partial declaration",
    "extern": "external runtime override",
    "implemented_by": "runtime implementation override",
}
FORBIDDEN_WHEN_QUALIFIED = frozenset({"sorryAx", "ofReduceBool", "trustCompiler"})
# These names are rejected even inside comments or literals. This deliberate
# conservatism closes string-interpolation holes without pretending this small
# checker is a complete Lean lexer.
FORBIDDEN_EVERYWHERE = FORBIDDEN_WHEN_QUALIFIED


class ScanError(ValueError):
    """A lexical region did not terminate."""


class AxiomReportError(ValueError):
    """A `#print axioms` entry was truncated or malformed."""


def scrub_literals_and_comments(source: str) -> str:
    """Blank comments/literals while preserving offsets and newlines."""

    output = list(source)
    length = len(source)
    index = 0

    def blank(start: int, stop: int) -> None:
        for position in range(start, stop):
            if output[position] != "\n":
                output[position] = " "

    while index < length:
        if source.startswith("--", index):
            stop = source.find("\n", index + 2)
            stop = length if stop == -1 else stop
            blank(index, stop)
            index = stop
            continue

        if source.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < length and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ScanError("unterminated block comment")
            blank(start, index)
            continue

        # Lean raw strings: r"..." and r#"..."# for any number of #s.
        if source[index] == "r" and (
            index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'")
        ):
            quote = index + 1
            while quote < length and source[quote] == "#":
                quote += 1
            if quote < length and source[quote] == '"':
                terminator = '"' + source[index + 1 : quote]
                stop = source.find(terminator, quote + 1)
                if stop == -1:
                    raise ScanError("unterminated raw string")
                stop += len(terminator)
                blank(index, stop)
                index = stop
                continue

        delimiter = source[index]
        if delimiter in {'"', "'"}:
            # Apostrophes in identifiers are not character-literal delimiters.
            if (
                delimiter == "'"
                and index > 0
                and (source[index - 1].isalnum() or source[index - 1] in "_'")
            ):
                index += 1
                continue
            start = index
            index += 1
            while index < length and source[index] != delimiter:
                index += 2 if source[index] == "\\" else 1
            if index == length:
                raise ScanError(f"unterminated {delimiter} literal")
            index += 1
            blank(start, index)
            continue

        if source[index] == "«":
            stop = source.find("»", index + 1)
            if stop == -1:
                raise ScanError("unterminated quoted identifier")
            stop += 1
            blank(index, stop)
            index = stop
            continue

        index += 1

    return "".join(output)


def scan_source(path: Path) -> list[str]:
    source = path.read_text(encoding="utf-8")
    findings: list[str] = []

    for match in forbidden_matches(source):
        word = match.group()
        offset = match.start()
        line = source.count("\n", 0, offset) + 1
        line_start = source.rfind("\n", 0, offset)
        column = offset - line_start
        findings.append(
            f"{path}:{line}:{column}: forbidden `{word}`: {FORBIDDEN[word]}"
        )

    return findings


def forbidden_matches(source: str) -> list[re.Match[str]]:
    tokens = list(TOKEN.finditer(scrub_literals_and_comments(source)))
    findings: dict[tuple[int, str], re.Match[str]] = {}
    for index, match in enumerate(tokens):
        word = match.group()
        if word not in FORBIDDEN:
            continue
        previous = tokens[index - 1].group() if index else ""
        previous_two = tokens[index - 2].group() if index > 1 else ""
        qualified = previous == "." and word not in FORBIDDEN_WHEN_QUALIFIED
        print_axioms = word == "axioms" and previous == "print" and previous_two == "#"
        if not qualified and not print_axioms:
            findings[(match.start(), word)] = match

    # Lean expressions inside `s!"...{...}..."` are executable, but a simple
    # literal scrubber cannot distinguish them from display text. Reject the
    # three compiler-trust escape hatches everywhere in the source so neither
    # interpolation nor future literal syntax can hide them.
    for match in TOKEN.finditer(source):
        word = match.group()
        if word in FORBIDDEN_EVERYWHERE:
            findings[(match.start(), word)] = match

    return [findings[key] for key in sorted(findings)]


def source_files(paths: Sequence[Path]) -> list[Path]:
    files: set[Path] = set()
    for path in paths:
        if path.is_file() and path.suffix == ".lean":
            files.add(path)
        elif path.is_dir():
            files.update(
                candidate
                for candidate in path.rglob("*.lean")
                if not SKIP_DIRECTORIES.intersection(candidate.parts)
            )
    return sorted(files)


def check_sources(paths: Sequence[Path]) -> int:
    files = source_files(paths)
    if not files:
        print("error: no Lean source files found", file=sys.stderr)
        return 2
    try:
        findings = [finding for path in files for finding in scan_source(path)]
    except (OSError, UnicodeError, ScanError) as error:
        print(f"Lean hygiene scan failed: {error}", file=sys.stderr)
        return 2
    if findings:
        print(*findings, sep="\n", file=sys.stderr)
        return 1
    print(f"Lean hygiene scan passed ({len(files)} source files).")
    return 0


def normalized_axiom_entries(lines: Sequence[str]) -> list[str]:
    """Join Lean's width-wrapped `#print axioms` diagnostics into entries."""

    entries: list[str] = []
    pending: list[str] = []
    for raw_line in lines:
        line = ANSI_ESCAPE.sub("", raw_line).strip()
        if pending:
            if not line:
                raise AxiomReportError("blank line inside wrapped axiom entry")
            pending.append(line)
            if line.endswith("]"):
                entries.append(" ".join(pending))
                pending = []
            continue
        if "depends on axioms: [" in line and not line.endswith("]"):
            if not line.startswith("'"):
                raise AxiomReportError(f"malformed axiom report line: {line}")
            pending = [line]
            continue
        entries.append(line)
    if pending:
        raise AxiomReportError(f"unterminated axiom report entry: {' '.join(pending)}")
    return entries


def check_axiom_report(path: Path) -> int:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        print(f"{path}: cannot read axiom report: {error}", file=sys.stderr)
        return 2

    try:
        entries = normalized_axiom_entries(lines)
    except AxiomReportError as error:
        print(f"{path}: {error}", file=sys.stderr)
        return 2

    audited = 0
    violations: list[str] = []
    for line in entries:
        match = AXIOM_LINE.fullmatch(line)
        if match is None:
            if "depends on axioms:" in line:
                print(f"{path}: malformed axiom report line: {line}", file=sys.stderr)
                return 2
            continue
        audited += 1
        rendered = match.group("axioms")
        dependencies = (
            set()
            if rendered is None
            else {item.strip() for item in rendered.split(",")}
        )
        unexpected = dependencies - ALLOWED_AXIOMS
        if unexpected:
            violations.append(f"nonstandard axioms {sorted(unexpected)}: {line}")

    if audited == 0:
        print(
            f"{path}: axiom report contained no audited declarations", file=sys.stderr
        )
        return 2
    if violations:
        print(*violations, sep="\n", file=sys.stderr)
        return 1
    print(f"Axiom report passed ({audited} declarations).")
    return 0


def self_test() -> None:
    harmless = r"""
-- axiom bad : False
/- partial def hidden := 0 /- unsafe def nested := 0 -/ -/
def prose := "sorry admit axiom unsafe partial"
def raw := r#"constant sorry unsafe"#
def quoted := «unsafe»
#print axioms Nat.add_comm
"""
    assert not scan_text(harmless)
    dangerous = """
axiom bad : False
unsafe def bad := by sorry
#check Lean.sorryAx
#check Lean.ofReduceBool
@[implemented_by bad] def override := 0
"""
    assert scan_text(dangerous) == {
        "axiom",
        "unsafe",
        "sorry",
        "sorryAx",
        "ofReduceBool",
        "implemented_by",
    }
    interpolation_bypass = r"""
set_option linter.deprecated false in
def bypass : String :=
  s!"{(let _proof : True := Lean.trustCompiler; 0)}"
"""
    assert scan_text(interpolation_bypass) == {"trustCompiler"}
    assert scan_text("-- Lean.trustCompiler is forbidden even in prose") == {
        "trustCompiler"
    }
    wrapped_axioms = [
        "'Cordis.Long.theorem_name' depends on axioms: [propext,",
        " Classical.choice,",
        " Quot.sound]",
        "'Cordis.Constructive' does not depend on any axioms",
    ]
    assert normalized_axiom_entries(wrapped_axioms) == [
        "'Cordis.Long.theorem_name' depends on axioms: [propext, Classical.choice, Quot.sound]",
        "'Cordis.Constructive' does not depend on any axioms",
    ]
    print("Lean hygiene scanner self-test passed.")


def scan_text(source: str) -> set[str]:
    return {match.group() for match in forbidden_matches(source)}


def main(arguments: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, default=[Path(".")])
    parser.add_argument("--axiom-report", type=Path)
    parser.add_argument("--self-test", action="store_true")
    options = parser.parse_args(arguments)
    if options.self_test:
        self_test()
    if options.axiom_report is not None:
        return check_axiom_report(options.axiom_report)
    return check_sources(options.paths)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
