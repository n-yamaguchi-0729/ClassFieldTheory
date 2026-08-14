#!/usr/bin/env python3
"""Check Class Field Theory documentation coverage and source-neutral prose.

The mathematical library must describe results by their content, not by a
location in one particular textbook.  This scanner therefore examines Lean
comments (never executable source) together with the maintained Markdown and
JSON documentation.  It also requires every Lean module to have a module
docstring.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[1]
LEAN_ROOT = WORKSPACE / "Lean4" / "ClassFieldTheory"
CANONICAL_ROOT = WORKSPACE / "Lean4" / "ClassFieldTheory.lean"
SCRIPT_DOCS_ROOT = HERE


@dataclass(frozen=True)
class DocumentationFragment:
    path: Path
    line: int
    text: str


FORBIDDEN = (
    (
        "textbook-facing wording",
        re.compile(
            r"\b(?:book|textbook|book-facing|book-faithful)\b|教科書|書籍",
            re.IGNORECASE,
        ),
    ),
    (
        "chapter citation",
        re.compile(r"\b(?:chapter|chap\.?)\s+(?:[IVXLCDM]+|\d+)", re.IGNORECASE),
    ),
    (
        "section citation",
        re.compile(r"§\s*(?:[IVXLCDM]+|\d+)", re.IGNORECASE),
    ),
    (
        "numbered source result",
        re.compile(
            r"\b(?:theorem|proposition|corollary|lemma|definition|prop\.?)\s*"
            r"(?:[-:]\s*)?"
            r"(?:[IVXLCDM]+\.\(?\d+(?:\.\d+)*\)?|\(?\d+(?:\.\d+)+\)?|\(\d+\))",
            re.IGNORECASE,
        ),
    ),
    (
        "bare Roman source result",
        re.compile(
            r"\b[IVXLCDM]+\.(?:\(\d+(?:\.\d+)*\)|\d+(?:\.\d+)+)",
            re.IGNORECASE,
        ),
    ),
    (
        "source-derived proposition filename",
        re.compile(r"\bProp\d+\.lean\b", re.IGNORECASE),
    ),
)

LEAN_ONLY_FORBIDDEN = (
    (
        "bare numbered source result",
        re.compile(r"(?<![\w.])(?:\(\d+\.\d+\)|\d+\.\d+)(?![\w.])"),
    ),
)

DECLARATION_START_RE = re.compile(
    r"^(?:(?:@\[[^\]]*\])\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|constant)\b",
    re.MULTILINE,
)


def lean_comment_fragments(path: Path, source: str) -> list[DocumentationFragment]:
    """Return line-oriented Lean comments while ignoring strings and code."""

    fragments: list[DocumentationFragment] = []
    i = 0
    line = 1
    length = len(source)
    while i < length:
        if source.startswith("--", i):
            start_line = line
            end = source.find("\n", i + 2)
            if end < 0:
                end = length
            fragments.append(DocumentationFragment(path, start_line, source[i + 2 : end]))
            line += source[i:end].count("\n")
            i = end
            continue
        if source.startswith("/-", i):
            start_line = line
            depth = 1
            j = i + 2
            while j < length and depth:
                if source.startswith("/-", j):
                    depth += 1
                    j += 2
                elif source.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            body = source[i + 2 : j - 2 if depth == 0 else j]
            for offset, text in enumerate(body.splitlines() or [body]):
                fragments.append(DocumentationFragment(path, start_line + offset, text))
            line += source[i:j].count("\n")
            i = j
            continue
        if source[i] == '"':
            i += 1
            while i < length:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == "\n":
                        line += 1
                    i += 1
            continue
        if source[i] == "\n":
            line += 1
        i += 1
    return fragments


def owned_lean_files(lean_root: Path) -> list[Path]:
    """Return the split canonical root and production-subtree sources."""

    paths = list(lean_root.rglob("*.lean"))
    if lean_root.resolve() == LEAN_ROOT.resolve() and CANONICAL_ROOT.is_file():
        paths.append(CANONICAL_ROOT)
    return sorted(paths)


def maintained_fragments(lean_root: Path, script_docs_root: Path) -> list[DocumentationFragment]:
    fragments: list[DocumentationFragment] = []
    for path in owned_lean_files(lean_root):
        fragments.extend(lean_comment_fragments(path, path.read_text(encoding="utf-8")))
    document_paths = sorted(lean_root.rglob("*.md"))
    document_paths += sorted(script_docs_root.rglob("*.md"))
    document_paths += sorted(script_docs_root.rglob("*.json"))
    for path in document_paths:
        for line, text in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            fragments.append(DocumentationFragment(path, line, text))
    return fragments


def module_docstring_missing(path: Path) -> bool:
    source = path.read_text(encoding="utf-8")
    module_doc = source.find("/-!")
    if module_doc < 0:
        return True
    first_declaration = DECLARATION_START_RE.search(source)
    return first_declaration is not None and module_doc > first_declaration.start()


def violations(
    lean_root: Path = LEAN_ROOT,
    script_docs_root: Path = SCRIPT_DOCS_ROOT,
) -> tuple[list[tuple[DocumentationFragment, str, str]], list[Path]]:
    prose_violations: list[tuple[DocumentationFragment, str, str]] = []
    for fragment in maintained_fragments(lean_root, script_docs_root):
        patterns = FORBIDDEN
        if fragment.path.suffix == ".lean":
            patterns += LEAN_ONLY_FORBIDDEN
        for label, pattern in patterns:
            match = pattern.search(fragment.text)
            if match:
                prose_violations.append((fragment, label, match.group(0)))
    missing = [path for path in owned_lean_files(lean_root) if module_docstring_missing(path)]
    return prose_violations, missing


def self_test() -> int:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        lean_root = root / "Lean4" / "ClassFieldTheory"
        docs_root = root / "scripts" / "ClassFieldTheory"
        lean_root.mkdir(parents=True)
        docs_root.mkdir(parents=True)
        good = lean_root / "Good.lean"
        good.write_text(
            'import Mathlib\n/-! # Local norm compatibility -/\n'
            '/-- Hilbert theorem 90 in multiplicative form. -/\n'
            'theorem good : True := by trivial\n'
            'def bookkeeping := "Chapter VI in a string is not documentation"\n',
            encoding="utf-8",
        )
        bad = lean_root / "Bad.lean"
        bad.write_text(
            'import Mathlib\n-- Chapter VI, Theorem 5.1\n'
            'theorem bad : True := by trivial\n',
            encoding="utf-8",
        )
        prose, missing = violations(lean_root, docs_root)
        labels = {label for _, label, _ in prose}
        if bad not in missing or good in missing:
            print("documentation self-test: module-doc detection failed", file=sys.stderr)
            return 1
        expected = {"chapter citation", "numbered source result"}
        if not expected <= labels:
            print(f"documentation self-test: missing detections: {expected - labels}", file=sys.stderr)
            return 1
    print("documentation self-test: OK")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    prose, missing = violations()
    for fragment, label, match in prose:
        relative = fragment.path.relative_to(WORKSPACE)
        print(f"{relative}:{fragment.line}: {label}: {match}", file=sys.stderr)
    for path in missing:
        relative = path.relative_to(WORKSPACE)
        print(f"{relative}: missing module docstring /-! ... -/", file=sys.stderr)
    if prose or missing:
        print(
            f"documentation contract: FAILED: {len(prose)} prose violations, "
            f"{len(missing)} modules without module docs",
            file=sys.stderr,
        )
        return 1
    module_count = len(owned_lean_files(LEAN_ROOT))
    print(f"documentation contract: OK: {module_count} documented modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
