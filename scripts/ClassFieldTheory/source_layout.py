#!/usr/bin/env python3
"""Shared paths for the Class Field Theory maintenance scripts.

``Lean4/ClassFieldTheory/`` is the single source root of the library and
``Lean4/ClassFieldTheory/ClassFieldTheory.lean`` is its canonical root module.
The source tree now deliberately includes local class field theory, Hasse--Arf,
Kronecker--Weber, and their shared infrastructure.  Discovering every Lean
file below that source root keeps the maintenance tools correct as future
global class field theory modules are added.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Iterator


SCRIPT_ROOT = Path(__file__).resolve().parent
WORKSPACE_ROOT = SCRIPT_ROOT.parents[1]
REPOSITORY_LEAN_ROOT = WORKSPACE_ROOT / "Lean4"
LEAN_ROOT = REPOSITORY_LEAN_ROOT / "ClassFieldTheory"
CANONICAL_ROOT = LEAN_ROOT / "ClassFieldTheory.lean"
DOCS_ROOT = SCRIPT_ROOT / "docs"


def lean_source_files() -> list[Path]:
    """Return every non-canonical Lean source owned by the library."""

    if not LEAN_ROOT.is_dir():
        raise FileNotFoundError(
            f"missing Class Field Theory source root: {LEAN_ROOT}"
        )
    return sorted(
        (
            path
            for path in LEAN_ROOT.rglob("*.lean")
            if path != CANONICAL_ROOT and ".lake" not in path.parts
        ),
        key=lambda path: path.relative_to(LEAN_ROOT).as_posix(),
    )


def contract_source_files() -> list[Path]:
    """Return all contract-owned sources, including the canonical outer root."""

    if not CANONICAL_ROOT.is_file():
        raise FileNotFoundError(
            "missing canonical Class Field Theory root: "
            f"{CANONICAL_ROOT}"
        )
    return [CANONICAL_ROOT, *lean_source_files()]


def source_relative_path(path: Path) -> str:
    """Return a stable contract path for a library-owned source."""

    return path.relative_to(LEAN_ROOT).as_posix()


def strip_lean_comments(text: str) -> str:
    """Blank nested Lean comments while preserving strings and line breaks.

    This is deliberately a lexical normalizer, not a Lean parser.  It knows the
    two Lean comment forms, nested ``/- ... -/`` comments, quoted strings, and
    string escapes.  Replacing comment characters with spaces keeps tokens on
    either side separated and makes line-oriented metrics insensitive to added
    module/declaration documentation.
    """

    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while index < len(text):
        character = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""

        if line_comment:
            if character in "\r\n":
                line_comment = False
                output.append(character)
            else:
                output.append(" ")
            index += 1
            continue

        if block_depth:
            if character == "/" and following == "-":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif character == "-" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                output.append(character if character in "\r\n" else " ")
                index += 1
            continue

        if in_string:
            output.append(character)
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue

        if character == '"':
            in_string = True
            output.append(character)
            index += 1
        elif character == "-" and following == "-":
            line_comment = True
            output.extend((" ", " "))
            index += 2
        elif character == "/" and following == "-":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
        else:
            output.append(character)
            index += 1
    return "".join(output)


def normalized_lean_code(text: str) -> str:
    """Return code-only Lean text stable under comment and blank-line edits."""

    code_lines = [
        line.rstrip()
        for line in strip_lean_comments(text).splitlines()
        if line.strip()
    ]
    return "\n".join(code_lines) + ("\n" if code_lines else "")


def lean_code_line_count(text: str) -> int:
    """Count nonblank lines after removing Lean comments."""

    return len(normalized_lean_code(text).splitlines())


def source_inventory(files: list[Path] | None = None) -> dict[str, object]:
    """Describe the exact, ordered module-file set covered by the contracts."""

    selected = files if files is not None else contract_source_files()
    modules = [source_relative_path(path) for path in selected]
    digest = hashlib.sha256()
    for module in modules:
        digest.update(module.encode("utf-8"))
        digest.update(b"\0")
    return {
        "schema_version": 1,
        "module_count": len(modules),
        "modules_sha256": digest.hexdigest(),
        "modules": modules,
    }


def source_code_sha256(files: list[Path] | None = None) -> str:
    """Hash source code while ignoring comments and blank lines."""

    selected = files if files is not None else contract_source_files()
    digest = hashlib.sha256()
    for path in selected:
        digest.update(source_relative_path(path).encode("utf-8"))
        digest.update(b"\0")
        digest.update(
            normalized_lean_code(
                path.read_text(encoding="utf-8", errors="replace")
            ).encode("utf-8")
        )
        digest.update(b"\0")
    return digest.hexdigest()


def module_source_entries() -> Iterator[Path]:
    """Yield existing top-level files/directories needed by a source-only copy."""

    for entry in sorted(LEAN_ROOT.iterdir(), key=lambda path: path.name):
        if entry == CANONICAL_ROOT:
            continue
        if entry.is_file() and entry.suffix == ".lean":
            yield entry
        elif entry.is_dir() and any(entry.rglob("*.lean")):
            yield entry
