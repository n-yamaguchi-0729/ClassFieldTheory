#!/usr/bin/env python3
"""Reject proof escapes and review theorem-scoped heartbeat exceptions.

Production sources may not contain proof placeholders, axiom declarations,
unsafe/partial declarations, lint suppressions, or source-level option changes.
The sole exception is an exact, reviewed ``maxHeartbeats`` override attached
to one theorem or lemma in the global Hilbert-symbol/product-formula B area.
Those exceptions are frozen by path, fully-qualified declaration name, and
integer value in ``docs/heartbeat-allowlist.json``.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tempfile
from typing import Iterable

from source_layout import (
    DOCS_ROOT,
    LEAN_ROOT,
    contract_source_files,
    source_relative_path,
)


DEFAULT_ALLOWLIST = DOCS_ROOT / "heartbeat-allowlist.json"
SCHEMA_VERSION = 1

ALLOWED_GLOBAL_HILBERT_PREFIX = (
    "GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/"
)
ALLOWED_PRODUCT_FORMULA_PATH = (
    "GlobalClassFieldTheory/Reciprocity/HilbertProductFormula.lean"
)

OPTION_LINE_RE = re.compile(
    r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+(?P<value>[0-9]+)"
    r"[ \t]+in[ \t]*$"
)
OPTION_TOKEN_RE = re.compile(r"\bset_option\b")
DECLARATION_RE = re.compile(
    r"^[ \t]*(?:private[ \t]+)?(?P<kind>theorem|lemma)[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NAMESPACE_RE = re.compile(
    r"^[ \t]*namespace[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)[ \t]*$"
)
SECTION_RE = re.compile(
    r"^[ \t]*section(?:[ \t]+[A-Za-z_][A-Za-z0-9_']*)?[ \t]*$"
)
END_RE = re.compile(
    r"^[ \t]*end(?:[ \t]+[A-Za-z_][A-Za-z0-9_'.]*)?[ \t]*$"
)

SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local)[ \t]+)*axiom\b",
    re.MULTILINE,
)
UNSAFE_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local)[ \t]+)*"
    r"unsafe[ \t]+(?:def|abbrev|instance|opaque)\b",
    re.MULTILINE,
)
PARTIAL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local)[ \t]+)*"
    r"partial[ \t]+def\b",
    re.MULTILINE,
)
NOLINT_RE = re.compile(r"\bnolint\b")
DIRECTIVE_RE = re.compile(
    r"^[ \t]*#[A-Za-z_][A-Za-z0-9_']*\b",
    re.MULTILINE,
)
EXAMPLE_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local|unsafe|partial)[ \t]+)*"
    r"example\b",
    re.MULTILINE,
)


@dataclass(frozen=True)
class HeartbeatAllowance:
    """One exact theorem-scoped ``maxHeartbeats`` exception."""

    path: str
    declaration: str
    option: str
    value: int
    reason: str

    @property
    def key(self) -> tuple[str, str, str, int]:
        return (self.path, self.declaration, self.option, self.value)


@dataclass(frozen=True)
class Diagnostic:
    """A stable source-policy diagnostic."""

    path: str
    line: int | None
    message: str

    def render(self) -> str:
        location = self.path
        if self.line is not None:
            location += f":{self.line}"
        return f"{location}: {self.message}"


def mask_noncode(source: str) -> str:
    """Blank comments, strings, and quoted identifiers, preserving newlines."""

    result: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    in_quoted_identifier = False
    while index < len(source):
        character = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""

        if line_comment:
            if character in "\r\n":
                line_comment = False
                result.append(character)
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth:
            if character == "/" and following == "-":
                block_depth += 1
                result.extend((" ", " "))
                index += 2
            elif character == "-" and following == "/":
                block_depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append(character if character in "\r\n" else " ")
                index += 1
            continue

        if in_string:
            if escaped:
                escaped = False
                result.append(character if character in "\r\n" else " ")
            elif character == "\\":
                escaped = True
                result.append(" ")
            elif character == '"':
                in_string = False
                result.append(" ")
            else:
                result.append(character if character in "\r\n" else " ")
            index += 1
            continue

        if in_quoted_identifier:
            if character == "»":
                in_quoted_identifier = False
            result.append(character if character in "\r\n" else " ")
            index += 1
            continue

        if character == "-" and following == "-":
            line_comment = True
            result.extend((" ", " "))
            index += 2
        elif character == "/" and following == "-":
            block_depth = 1
            result.extend((" ", " "))
            index += 2
        elif character == '"':
            in_string = True
            result.append(" ")
            index += 1
        elif character == "«":
            in_quoted_identifier = True
            result.append(" ")
            index += 1
        else:
            result.append(character)
            index += 1
    return "".join(result)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def valid_allowlist_path(path: str) -> bool:
    candidate = PurePosixPath(path)
    if candidate.is_absolute() or ".." in candidate.parts or path != candidate.as_posix():
        return False
    if candidate.suffix != ".lean":
        return False
    return (
        path.startswith(ALLOWED_GLOBAL_HILBERT_PREFIX)
        or path == ALLOWED_PRODUCT_FORMULA_PATH
    )


def parse_allowlist(payload: object) -> tuple[list[HeartbeatAllowance], list[str]]:
    """Validate and decode the reviewed heartbeat manifest."""

    errors: list[str] = []
    if not isinstance(payload, dict):
        return [], ["allowlist root must be an object"]
    if set(payload) != {"schema_version", "entries"}:
        errors.append("allowlist root must contain only schema_version and entries")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"allowlist schema_version must be {SCHEMA_VERSION}")
    raw_entries = payload.get("entries")
    if not isinstance(raw_entries, list):
        return [], [*errors, "allowlist entries must be an array"]

    entries: list[HeartbeatAllowance] = []
    expected_fields = {"path", "declaration", "option", "value", "reason"}
    seen_keys: set[tuple[str, str, str, int]] = set()
    seen_declarations: set[str] = set()
    for index, raw in enumerate(raw_entries):
        label = f"entries[{index}]"
        if not isinstance(raw, dict):
            errors.append(f"{label} must be an object")
            continue
        if set(raw) != expected_fields:
            errors.append(f"{label} must contain exactly {sorted(expected_fields)!r}")
            continue
        path = raw.get("path")
        declaration = raw.get("declaration")
        option = raw.get("option")
        value = raw.get("value")
        reason = raw.get("reason")
        if not isinstance(path, str) or not valid_allowlist_path(path):
            errors.append(f"{label}.path is not an allowed B-area Lean path")
        if (
            not isinstance(declaration, str)
            or not declaration.startswith("GlobalClassFieldTheory.Reciprocity.")
            or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", declaration)
        ):
            errors.append(f"{label}.declaration must be a fully-qualified reciprocity name")
        if option != "maxHeartbeats":
            errors.append(f"{label}.option must be maxHeartbeats")
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            errors.append(f"{label}.value must be a positive integer")
        if not isinstance(reason, str) or not reason.strip():
            errors.append(f"{label}.reason must be nonempty")
        if any(
            (
                not isinstance(path, str),
                not isinstance(declaration, str),
                option != "maxHeartbeats",
                isinstance(value, bool) or not isinstance(value, int) or value <= 0,
                not isinstance(reason, str) or not reason.strip(),
            )
        ):
            continue
        entry = HeartbeatAllowance(path, declaration, option, value, reason)
        if entry.key in seen_keys:
            errors.append(f"duplicate heartbeat allowlist entry: {entry.key!r}")
            continue
        if declaration in seen_declarations:
            errors.append(f"multiple heartbeat entries target {declaration}")
            continue
        seen_keys.add(entry.key)
        seen_declarations.add(declaration)
        entries.append(entry)
    return entries, errors


def namespace_before_lines(lines: list[str]) -> list[tuple[str, ...]]:
    """Return the namespace path active before each masked source line."""

    scopes: list[tuple[str, tuple[str, ...]]] = []
    result: list[tuple[str, ...]] = []
    for line in lines:
        namespace: list[str] = []
        for kind, parts in scopes:
            if kind == "namespace":
                namespace.extend(parts)
        result.append(tuple(namespace))
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            scopes.append(("namespace", tuple(namespace_match.group("name").split("."))))
        elif SECTION_RE.match(line):
            scopes.append(("section", ()))
        elif END_RE.match(line) and scopes:
            scopes.pop()
    return result


def next_code_line(lines: list[str], index: int) -> int | None:
    for candidate in range(index + 1, len(lines)):
        if lines[candidate].strip():
            return candidate
    return None


def scan_source(
    relative_path: str,
    source: str,
    allowances: Iterable[HeartbeatAllowance],
) -> tuple[list[Diagnostic], set[tuple[str, str, str, int]]]:
    """Check one Lean source and return diagnostics plus matched allowances."""

    masked = mask_noncode(source)
    lines = masked.splitlines()
    namespaces = namespace_before_lines(lines)
    diagnostics: list[Diagnostic] = []
    matched: set[tuple[str, str, str, int]] = set()
    by_key = {entry.key: entry for entry in allowances}

    forbidden_patterns = (
        (SORRY_RE, "proof placeholder sorry/admit is forbidden"),
        (AXIOM_RE, "axiom declaration is forbidden"),
        (UNSAFE_RE, "unsafe declaration is forbidden"),
        (PARTIAL_RE, "partial definition is forbidden"),
        (NOLINT_RE, "nolint suppression is forbidden"),
        (DIRECTIVE_RE, "production command directives are forbidden"),
        (EXAMPLE_RE, "production example commands are forbidden"),
    )
    for pattern, message in forbidden_patterns:
        for occurrence in pattern.finditer(masked):
            diagnostics.append(
                Diagnostic(relative_path, line_number(masked, occurrence.start()), message)
            )

    for index, line in enumerate(lines):
        occurrences = list(OPTION_TOKEN_RE.finditer(line))
        if not occurrences:
            continue
        source_line = index + 1
        option_match = OPTION_LINE_RE.fullmatch(line)
        if len(occurrences) != 1 or option_match is None:
            diagnostics.append(
                Diagnostic(
                    relative_path,
                    source_line,
                    "source-level set_option is forbidden unless it is one exact "
                    "theorem-scoped maxHeartbeats allowance",
                )
            )
            continue
        target_index = next_code_line(lines, index)
        if target_index is None:
            diagnostics.append(
                Diagnostic(relative_path, source_line, "heartbeat option has no target declaration")
            )
            continue
        declaration_match = DECLARATION_RE.match(lines[target_index])
        if declaration_match is None:
            diagnostics.append(
                Diagnostic(
                    relative_path,
                    source_line,
                    "heartbeat option must immediately scope one top-level theorem or lemma",
                )
            )
            continue
        short_name = declaration_match.group("name")
        full_parts = (*namespaces[index], *short_name.split("."))
        declaration = ".".join(full_parts)
        value = int(option_match.group("value"))
        key = (relative_path, declaration, "maxHeartbeats", value)
        if key not in by_key:
            diagnostics.append(
                Diagnostic(
                    relative_path,
                    source_line,
                    f"unreviewed heartbeat override for {declaration} at value {value}",
                )
            )
            continue
        if key in matched:
            diagnostics.append(
                Diagnostic(relative_path, source_line, "heartbeat allowance is used more than once")
            )
            continue
        matched.add(key)
    return diagnostics, matched


def check_sources(
    sources: Iterable[tuple[str, str]],
    allowances: list[HeartbeatAllowance],
) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    matched: set[tuple[str, str, str, int]] = set()
    for relative_path, source in sources:
        local_diagnostics, local_matched = scan_source(
            relative_path, source, allowances
        )
        diagnostics.extend(local_diagnostics)
        matched.update(local_matched)
    for entry in allowances:
        if entry.key not in matched:
            diagnostics.append(
                Diagnostic(
                    entry.path,
                    None,
                    f"stale heartbeat allowance for {entry.declaration} at value {entry.value}",
                )
            )
    return diagnostics


def fixture_entry(**changes: object) -> HeartbeatAllowance:
    values: dict[str, object] = {
        "path": "GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/Example.lean",
        "declaration": "GlobalClassFieldTheory.Reciprocity.allowedBridge",
        "option": "maxHeartbeats",
        "value": 4_000_000,
        "reason": "Synthetic B comparison fixture.",
    }
    values.update(changes)
    return HeartbeatAllowance(**values)  # type: ignore[arg-type]


def run_self_tests() -> None:
    entry = fixture_entry()
    allowed = """/-! Fixture. -/
namespace GlobalClassFieldTheory
namespace Reciprocity

set_option maxHeartbeats 4000000 in
/- A comment mentioning sorry, admit, axiom, nolint, set_option, #eval, and
   private example. -/
theorem allowedBridge : True := by
  have text := "sorry admit axiom nolint set_option #eval private example"
  trivial

end Reciprocity
end GlobalClassFieldTheory
"""
    assert not check_sources([(entry.path, allowed)], [entry])
    private_allowed = allowed.replace(
        "theorem allowedBridge", "private theorem allowedBridge", 1
    )
    assert not check_sources([(entry.path, private_allowed)], [entry])

    cases = {
        "wrong value": allowed.replace("4000000", "4000001", 1),
        "wrong declaration": allowed.replace("allowedBridge", "otherBridge", 1),
        "global option": allowed.replace("maxHeartbeats 4000000 in", "maxHeartbeats 4000000", 1),
        "other option": allowed.replace("maxHeartbeats 4000000", "maxRecDepth 4000000", 1),
        "sorry": allowed.replace("  trivial", "  sorry", 1),
        "admit": allowed.replace("  trivial", "  admit", 1),
        "axiom": allowed.replace("theorem allowedBridge : True := by", "axiom escaped : True\ntheorem allowedBridge : True := by", 1),
        "nolint": allowed.replace("theorem allowedBridge", "@[nolint] theorem allowedBridge", 1),
        "unsafe": allowed.replace("theorem allowedBridge : True := by", "unsafe def escaped : Nat := 0\ntheorem allowedBridge : True := by", 1),
        "partial": allowed.replace("theorem allowedBridge : True := by", "partial def escaped : Nat := escaped\ntheorem allowedBridge : True := by", 1),
        "directive": allowed.replace(
            "theorem allowedBridge : True := by",
            "#eval 1\ntheorem allowedBridge : True := by",
            1,
        ),
        "modified example": allowed.replace(
            "theorem allowedBridge : True := by",
            "private example : True := by trivial\ntheorem allowedBridge : True := by",
            1,
        ),
    }
    for label, source in cases.items():
        assert check_sources([(entry.path, source)], [entry]), label

    other_b_path = (
        "GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/Other.lean"
    )
    assert check_sources([(other_b_path, allowed)], [entry]), "wrong source path"

    wrong_path = fixture_entry(path="GlobalClassFieldTheory/Reciprocity/Other.lean")
    payload = {
        "schema_version": SCHEMA_VERSION,
        "entries": [
            {
                "path": wrong_path.path,
                "declaration": wrong_path.declaration,
                "option": wrong_path.option,
                "value": wrong_path.value,
                "reason": wrong_path.reason,
            }
        ],
    }
    _, errors = parse_allowlist(payload)
    assert errors
    entries, errors = parse_allowlist({"schema_version": SCHEMA_VERSION, "entries": []})
    assert not entries and not errors

    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "allowlist.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        assert path.is_file()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allowlist", type=Path, default=DEFAULT_ALLOWLIST)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(f"source-policy self-test: FAILED: {error}", file=sys.stderr)
            return 1
        print("source-policy self-test: OK")
        return 0

    try:
        payload = json.loads(args.allowlist.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"source-policy: allowlist is missing: {args.allowlist}", file=sys.stderr)
        return 1
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"source-policy: cannot read allowlist: {error}", file=sys.stderr)
        return 1
    allowances, manifest_errors = parse_allowlist(payload)
    if manifest_errors:
        for error in manifest_errors:
            print(f"source-policy: allowlist: {error}", file=sys.stderr)
        print(
            f"source-policy: FAILED ({len(manifest_errors)} allowlist diagnostics)",
            file=sys.stderr,
        )
        return 1

    sources = [
        (
            source_relative_path(path),
            path.read_text(encoding="utf-8", errors="replace"),
        )
        for path in contract_source_files()
    ]
    diagnostics = check_sources(sources, allowances)
    for diagnostic in diagnostics:
        print(f"source-policy: {diagnostic.render()}", file=sys.stderr)
    if diagnostics:
        print(
            f"source-policy: FAILED ({len(diagnostics)} diagnostics)",
            file=sys.stderr,
        )
        return 1
    print(
        "source-policy: OK "
        f"({len(sources)} modules, {len(allowances)} heartbeat allowances)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
