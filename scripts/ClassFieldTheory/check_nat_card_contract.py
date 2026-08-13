#!/usr/bin/env python3
"""Audit uses of Mathlib's canonical finite-cardinality API.

`Nat.card` maps infinite types to zero.  This checker therefore inventories
sites whose finite source is not lexically visible for follow-up semantic
review, while its hard gate forbids recreating `Nat.card` or Mathlib's
bijectivity lemmas under root-namespace compatibility names. It also rejects
explicit `@Nat.card` applications, whose old extra `Finite` argument does not
belong to Mathlib's canonical signature. General cardinal-valued code should
use `Cardinal.mk`. The semantic inventory is scoped to Class Field Theory; the
removed root-level compatibility names are forbidden repository-wide.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from source_layout import LEAN_ROOT, REPOSITORY_LEAN_ROOT, lean_source_files


ROOT = LEAN_ROOT

DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|local|scoped)\s+)*"
    r"(?:def|theorem|lemma|instance|structure|class|abbrev)\s+([^\s(:{]+)"
)
NAT_CARD = re.compile(r"\bNat\.card\b")
LEGACY_API = re.compile(
    r"(?:cardOfFinite|bijective_of_cardOfFinite_le|@Nat\.card\b)"
)
EVIDENCE = (
    ("explicit_finite", re.compile(r"\[(?:Finite|Fintype)\b")),
    ("finite_argument", re.compile(r"\b(?:Finite|Fintype)\s*\(")),
    (
        "local_finite_instance",
        re.compile(
            r"\b(?:letI|haveI)\b[^\n]*(?:Finite|Fintype)|"
            r"\b(?:Fintype\.ofFinite|Finite\.of_|Finite\.of_equiv)\b"
        ),
    ),
    (
        "finite_bundle",
        re.compile(
            r"\b(?:FiniteAbstractExtension|FiniteAbstractField|"
            r"FiniteCyclicSubextension|FiniteGaloisSubextension|"
            r"FiniteAbelianSubextension|FiniteIntermediateField)\b"
        ),
    ),
)


def strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def declaration_starts(lines: list[str]) -> list[tuple[int, str]]:
    starts: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        match = DECLARATION.match(strip_line_comment(line))
        if match:
            starts.append((index, match.group(1)))
    return starts


def enclosing_declaration(
    starts: list[tuple[int, str]], line_index: int
) -> tuple[int, str]:
    result = (0, "<module>")
    for start, name in starts:
        if start > line_index:
            break
        result = (start, name)
    return result


def audit_file(path: Path) -> list[dict[str, object]]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    starts = declaration_starts(lines)
    findings: list[dict[str, object]] = []
    for index, line in enumerate(lines):
        if not NAT_CARD.search(strip_line_comment(line)):
            continue
        declaration_start, declaration = enclosing_declaration(starts, index)
        # Include section variables immediately above the declaration while
        # keeping the window narrow enough that unrelated instances do not
        # accidentally certify a later use.
        context_start = max(0, declaration_start - 40)
        context = "\n".join(lines[context_start : index + 1])
        evidence = [name for name, pattern in EVIDENCE if pattern.search(context)]
        findings.append(
            {
                "file": path.relative_to(ROOT).as_posix(),
                "line": index + 1,
                "declaration": declaration,
                "evidence": evidence,
            }
        )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--report-all",
        action="store_true",
        help="include certified sites as well as sites without visible evidence",
    )
    args = parser.parse_args()

    source_files = lean_source_files()
    package_source_files = sorted(REPOSITORY_LEAN_ROOT.rglob("*.lean"))
    legacy_sites: list[tuple[str, int]] = []
    for path in package_source_files:
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8", errors="replace").splitlines(),
            start=1,
        ):
            if LEGACY_API.search(strip_line_comment(line)):
                legacy_sites.append(
                    (
                        path.relative_to(REPOSITORY_LEAN_ROOT).as_posix(),
                        line_number,
                    )
                )

    findings = [finding for path in source_files for finding in audit_file(path)]
    risky = [
        finding
        for finding in findings
        if not finding["evidence"]
    ]
    reported = findings if args.report_all else (risky if args.json else [])
    if args.json:
        print(
            json.dumps(
                {
                    "nat_card_sites": len(findings),
                    "visible_finite_source": len(findings) - len(risky),
                    "missing_visible_finite_source": len(risky),
                    "legacy_api_sites": len(legacy_sites),
                    "sites": reported,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        for finding in reported:
            print(
                f"{finding['file']}:{finding['line']}: "
                f"{finding['declaration']}: Nat.card has no visible Finite/Fintype source"
            )
    for file_name, line_number in legacy_sites:
        print(
            f"{file_name}:{line_number}: legacy finite-cardinality API name",
            file=sys.stderr,
        )
    if legacy_sites:
        print(
            "nat-card-contract: FAILED "
            f"({len(legacy_sites)} legacy API sites)",
            file=sys.stderr,
        )
        return 1
    print(
        "nat-card-contract: OK "
        f"(no legacy API; {len(risky)} Nat.card sites require semantic review "
        "beyond the static evidence heuristic)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
