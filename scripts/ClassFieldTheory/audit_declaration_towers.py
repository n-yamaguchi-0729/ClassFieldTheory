#!/usr/bin/env python3
"""Audit declaration-level elaboration risks without invoking Lean.

The scanner covers every source owned by ``Lean4/ClassFieldTheory`` and keeps
four costs separate:

* local-instance towers embedded in public declaration signatures;
* the same heavy instance target rebuilt in the declaration body;
* local-instance towers hidden in structure/inductive constructor payloads;
* very large declaration spans;
* broad ``simp``/``simpa`` tactics and ``change`` tactics.

This is a lexical contract, not a Lean parser.  It deliberately accepts only
top-level declarations and prefers an explicit ``:= by`` boundary.  A
theorem/lemma with a term proof falls back to its last ``:=`` token; ambiguous
definitions are still measured for span and tactics but omitted from signature
metrics.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter
import json
from pathlib import Path
import re
import sys
import time


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from source_layout import (  # noqa: E402
    contract_source_files,
    source_inventory,
    source_relative_path,
    strip_lean_comments,
)


SCHEMA_VERSION = 2
DECLARATION_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "opaque",
    "axiom",
)
MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "scoped",
    "local",
)
DECLARATION_RE = re.compile(
    r"^(?:(?:@\[[^\]]*\])\s*)*"
    rf"(?P<mods>(?:(?:{'|'.join(MODIFIERS)})\s+)*)"
    rf"(?P<kind>{'|'.join(DECLARATION_KINDS)})\b"
    r"(?:\s+(?P<name>[^\s:({\[]+))?"
)
TOP_LEVEL_COMMAND_RE = re.compile(
    r"^(?:@\[|"
    rf"(?:(?:{'|'.join(MODIFIERS)})\s+)*(?:{'|'.join(DECLARATION_KINDS)})\b|"
    r"(?:namespace|section|end|variable|open|export|include|omit|attribute|"
    r"set_option|initialize|macro|syntax|elab|notation|infix|prefix|postfix)\b)"
)
BODY_BY_RE = re.compile(r":=\s*by\b")
ASSIGN_RE = re.compile(r":=")
LET_I_RE = re.compile(r"\bletI\b")
INFER_INSTANCE_RE = re.compile(r"\binferInstance\b")
CHANGE_RE = re.compile(r"\bchange\b")
BROAD_SIMP_LINE_RE = re.compile(
    r"(?:^\s*(?:[·*+-]\s*)?|(?:\bby|<;>)\s+)"
    r"(?:simpa|simp)(?:_all)?\b(?!\s+only\b)"
)
LET_I_TARGET_RE = re.compile(
    r"\bletI(?:\s+[^\s:]+)?\s*:\s*(?P<target>.*?)(?=\s*:=)",
    re.DOTALL,
)
HEAVY_TARGET_RE = re.compile(
    r"^(?:FiniteDimensional|NumberField|IsScalarTower|IsGalois|"
    r"IsAbelianGalois|Module\.Finite|Algebra\.IsAlgebraic|"
    r"Algebra\.IsSeparable)\b"
)
HEAVY_PATTERNS = {
    "finiteDimensionalTrans": re.compile(r"\bFiniteDimensional\.trans\b"),
    "numberFieldOfModuleFinite": re.compile(
        r"\bNumberField\.of_module_finite\b"
    ),
    "scalarTowerOfAlgebraMap": re.compile(
        r"\bIsScalarTower\.of_algebraMap_eq'?\b"
    ),
    "isAbelianGaloisOfAlgHom": re.compile(
        r"\bIsAbelianGalois\.of_algHom\b"
    ),
    "abstractFixedFieldFiniteDimensional": re.compile(
        r"\babstractFixedField_finiteDimensional\b"
    ),
    "abstractRelativeFixedFieldFiniteDimensional": re.compile(
        r"\babstractRelativeFixedField_finiteDimensional\b"
    ),
}
CONTRACT_CEILING_KEYS = (
    "public_signature_letI_declarations",
    "public_signature_letI_total",
    "public_signature_heavy_target_total",
    "signature_body_duplicate_target_declarations",
    "signature_body_duplicate_target_total",
    "signature_body_duplicate_constructor_total",
    "container_payload_letI_declarations",
    "container_payload_letI_total",
    "container_payload_heavy_target_total",
    "declarations_over_100_lines",
    "declarations_over_150_lines",
    "declarations_over_200_lines",
    "max_declaration_span",
    "max_public_signature_letI",
    "max_duplicate_heavy_targets",
    "max_container_payload_letI",
    "broad_simp_total",
    "change_total",
)

CONTAINER_KINDS = frozenset({"structure", "class", "inductive"})


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=25)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--json", action="store_true", help="print full JSON")
    output.add_argument(
        "--contract-json",
        action="store_true",
        help="print the compact current report and ceiling candidate",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run deterministic parser tests without reading Lean sources",
    )
    return parser.parse_args()


def normalize_target(target: str) -> str:
    return " ".join(target.split())


def heavy_targets(text: str) -> Counter[str]:
    targets = Counter()
    for match in LET_I_TARGET_RE.finditer(text):
        target = normalize_target(match.group("target"))
        if HEAVY_TARGET_RE.match(target):
            targets[target] += 1
    return targets


def pattern_counts(text: str) -> dict[str, int]:
    return {
        "letI": len(LET_I_RE.findall(text)),
        "inferInstance": len(INFER_INSTANCE_RE.findall(text)),
        **{
            name: len(pattern.findall(text))
            for name, pattern in HEAVY_PATTERNS.items()
        },
    }


def broad_simp_count(text: str) -> int:
    return sum(bool(BROAD_SIMP_LINE_RE.search(line)) for line in text.splitlines())


def declaration_name(
    match: re.Match[str], lines: list[str], start: int, ordinal: int
) -> str:
    if match.group("name"):
        return str(match.group("name"))
    for line in lines[start + 1 :]:
        stripped = line.strip()
        if not stripped:
            continue
        candidate = re.match(r"([^\s:({\[]+)", stripped)
        if candidate:
            return candidate.group(1)
        break
    return f"<anonymous-{ordinal}>"


def body_boundary(segment: str, kind: str) -> re.Match[str] | None:
    explicit = BODY_BY_RE.search(segment)
    if explicit is not None:
        return explicit
    if kind not in {"theorem", "lemma"}:
        return None
    assignments = list(ASSIGN_RE.finditer(segment))
    return assignments[-1] if assignments else None


def declarations_from_code(
    code: str, *, module: str, path: str
) -> list[dict[str, object]]:
    lines = code.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    boundaries: list[int] = []
    for index, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        if TOP_LEVEL_COMMAND_RE.match(line):
            boundaries.append(index)
        match = DECLARATION_RE.match(line)
        if match:
            starts.append((index, match))
    boundary_set = sorted({*boundaries, len(lines)})
    rows: list[dict[str, object]] = []
    for ordinal, (start, match) in enumerate(starts, 1):
        end = boundary_set[bisect_right(boundary_set, start)]
        segment = "\n".join(lines[start:end])
        kind = str(match.group("kind"))
        modifiers = tuple(str(match.group("mods") or "").split())
        boundary = body_boundary(segment, kind)
        signature = segment[: boundary.start()] if boundary else ""
        body = segment[boundary.end() :] if boundary else segment
        signature_counts = pattern_counts(signature)
        body_counts = pattern_counts(body)
        signature_targets = heavy_targets(signature)
        body_targets = heavy_targets(body)
        duplicated_targets = signature_targets & body_targets
        duplicated_constructors = {
            name: min(signature_counts[name], body_counts[name])
            for name in HEAVY_PATTERNS
        }
        rows.append(
            {
                "module": module,
                "path": path,
                "name": declaration_name(match, lines, start, ordinal),
                "kind": kind,
                "line": start + 1,
                "span": end - start,
                "public": not ({"private", "local"} & set(modifiers)),
                "has_body_boundary": boundary is not None,
                "signature": signature_counts,
                "body": body_counts,
                "container_payload": kind in CONTAINER_KINDS,
                "signature_heavy_targets": dict(signature_targets),
                "body_heavy_targets": dict(body_targets),
                "duplicate_heavy_targets": dict(duplicated_targets),
                "duplicate_heavy_target_count": sum(duplicated_targets.values()),
                "duplicate_constructor_count": sum(
                    duplicated_constructors.values()
                ),
                "broad_simp": broad_simp_count(segment),
                "change": len(CHANGE_RE.findall(segment)),
            }
        )
    return rows


def declarations_from_text(
    text: str, *, module: str, path: str
) -> list[dict[str, object]]:
    return declarations_from_code(
        strip_lean_comments(text), module=module, path=path
    )


def audit_sources(
    paths: list[Path] | None = None, *, limit: int = 25
) -> dict[str, object]:
    selected = contract_source_files() if paths is None else paths
    rows: list[dict[str, object]] = []
    broad_total = 0
    change_total = 0
    for path in selected:
        text = path.read_text(encoding="utf-8", errors="replace")
        code = strip_lean_comments(text)
        broad_total += broad_simp_count(code)
        change_total += len(CHANGE_RE.findall(code))
        rows.extend(
            declarations_from_code(
                code,
                module=source_relative_path(path.with_suffix(""))
                .replace("/", "."),
                path=source_relative_path(path),
            )
        )
    public_signature = [
        row
        for row in rows
        if row["public"] and row["has_body_boundary"]
    ]
    signature_towers = [
        row for row in public_signature if int(row["signature"]["letI"])
    ]
    duplicated = [
        row for row in public_signature if row["duplicate_heavy_target_count"]
    ]
    container_payloads = [row for row in rows if row["container_payload"]]
    container_payload_towers = [
        row for row in container_payloads if int(row["body"]["letI"])
    ]
    spans = [int(row["span"]) for row in rows]
    summary = {
        "files": len(selected),
        "parsed_declarations": len(rows),
        "public_declarations_with_body_boundary": len(public_signature),
        "public_signature_letI_declarations": len(signature_towers),
        "public_signature_letI_total": sum(
            int(row["signature"]["letI"]) for row in public_signature
        ),
        "public_signature_heavy_target_total": sum(
            sum(int(value) for value in row["signature_heavy_targets"].values())
            for row in public_signature
        ),
        "signature_body_duplicate_target_declarations": len(duplicated),
        "signature_body_duplicate_target_total": sum(
            int(row["duplicate_heavy_target_count"]) for row in public_signature
        ),
        "signature_body_duplicate_constructor_total": sum(
            int(row["duplicate_constructor_count"]) for row in public_signature
        ),
        "container_payload_letI_declarations": len(container_payload_towers),
        "container_payload_letI_total": sum(
            int(row["body"]["letI"]) for row in container_payloads
        ),
        "container_payload_heavy_target_total": sum(
            sum(int(value) for value in row["body_heavy_targets"].values())
            for row in container_payloads
        ),
        "declarations_over_100_lines": sum(span > 100 for span in spans),
        "declarations_over_150_lines": sum(span > 150 for span in spans),
        "declarations_over_200_lines": sum(span > 200 for span in spans),
        "max_declaration_span": max(spans, default=0),
        "max_public_signature_letI": max(
            (int(row["signature"]["letI"]) for row in public_signature),
            default=0,
        ),
        "max_duplicate_heavy_targets": max(
            (int(row["duplicate_heavy_target_count"]) for row in public_signature),
            default=0,
        ),
        "max_container_payload_letI": max(
            (int(row["body"]["letI"]) for row in container_payloads),
            default=0,
        ),
        "broad_simp_total": broad_total,
        "change_total": change_total,
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": source_inventory(selected),
        "summary": summary,
        "top_declaration_spans": sorted(
            rows,
            key=lambda row: (-int(row["span"]), str(row["module"]), int(row["line"])),
        )[:limit],
        "top_signature_towers": sorted(
            signature_towers,
            key=lambda row: (
                -int(row["signature"]["letI"]),
                -sum(int(value) for value in row["signature_heavy_targets"].values()),
                -int(row["span"]),
                str(row["module"]),
            ),
        )[:limit],
        "top_duplicated_towers": sorted(
            duplicated,
            key=lambda row: (
                -int(row["duplicate_heavy_target_count"]),
                -int(row["duplicate_constructor_count"]),
                -int(row["span"]),
                str(row["module"]),
            ),
        )[:limit],
        "top_container_payload_towers": sorted(
            container_payload_towers,
            key=lambda row: (
                -int(row["body"]["letI"]),
                -sum(int(value) for value in row["body_heavy_targets"].values()),
                -int(row["span"]),
                str(row["module"]),
            ),
        )[:limit],
        "top_broad_simp": sorted(
            (row for row in rows if row["broad_simp"]),
            key=lambda row: (
                -int(row["broad_simp"]),
                -int(row["span"]),
                str(row["module"]),
            ),
        )[:limit],
    }


def compact_contract(payload: dict[str, object], *, hotspot_limit: int = 10) -> dict[str, object]:
    inventory = payload["source_inventory"]
    summary = payload["summary"]
    assert isinstance(inventory, dict)
    assert isinstance(summary, dict)

    def hotspot(row: dict[str, object]) -> dict[str, object]:
        return {
            "module": row["module"],
            "line": row["line"],
            "name": row["name"],
            "span": row["span"],
            "signature_letI": row["signature"]["letI"],
            "duplicate_heavy_targets": row["duplicate_heavy_target_count"],
            "container_payload_letI": (
                row["body"]["letI"] if row["container_payload"] else 0
            ),
            "broad_simp": row["broad_simp"],
        }

    return {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": {
            "module_count": inventory["module_count"],
            "modules_sha256": inventory["modules_sha256"],
        },
        "ceilings": {key: int(summary[key]) for key in CONTRACT_CEILING_KEYS},
        "current_report": {key: int(summary[key]) for key in CONTRACT_CEILING_KEYS},
        "hotspots": {
            "declaration_spans": [
                hotspot(row)
                for row in payload["top_declaration_spans"][:hotspot_limit]
            ],
            "signature_towers": [
                hotspot(row)
                for row in payload["top_signature_towers"][:hotspot_limit]
            ],
            "duplicated_towers": [
                hotspot(row)
                for row in payload["top_duplicated_towers"][:hotspot_limit]
            ],
            "container_payload_towers": [
                hotspot(row)
                for row in payload["top_container_payload_towers"][:hotspot_limit]
            ],
            "broad_simp": [
                hotspot(row)
                for row in payload["top_broad_simp"][:hotspot_limit]
            ],
        },
    }


def run_self_tests() -> None:
    source = """
theorem publicTower (K E : Type*) [Field K] [Field E] :
    letI : NumberField E := NumberField.of_module_finite K E
    True := by
  letI : NumberField E := NumberField.of_module_finite K E
  simp

private theorem hiddenTower :
    letI : FiniteDimensional Nat Nat := inferInstance
    True := by
  trivial

inductive HiddenPayload (K E : Type*) where
  | ofTower (
      proof :
        letI : NumberField E := NumberField.of_module_finite K E
        True)

theorem longEnough : True := by
  change True
  trivial
"""
    rows = declarations_from_text(source, module="Example", path="Example.lean")
    assert len(rows) == 4, rows
    public = rows[0]
    assert public["public"]
    assert public["signature"]["letI"] == 1
    assert public["body"]["letI"] == 1
    assert public["duplicate_heavy_target_count"] == 1
    assert public["broad_simp"] == 1
    assert not rows[1]["public"]
    assert rows[2]["container_payload"]
    assert rows[2]["body"]["letI"] == 1
    assert rows[2]["body_heavy_targets"]
    assert rows[3]["change"] == 1


def row_label(row: dict[str, object]) -> str:
    return f"{row['module']}:{row['line']}::{row['name']}"


def main() -> int:
    args = parse_args()
    if args.limit <= 0:
        raise SystemExit("--limit must be positive")
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(f"declaration-tower-audit self-test: FAILED: {error}", file=sys.stderr)
            return 1
        print("declaration-tower-audit self-test: OK")
        return 0
    started = time.perf_counter()
    payload = audit_sources(limit=args.limit)
    elapsed = time.perf_counter() - started
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0
    if args.contract_json:
        print(json.dumps(compact_contract(payload), ensure_ascii=False, indent=2))
        return 0
    summary = payload["summary"]
    print(
        "declaration-tower-audit: "
        f"files={summary['files']} declarations={summary['parsed_declarations']} "
        f"signature-letI={summary['public_signature_letI_total']} "
        f"duplicate-targets={summary['signature_body_duplicate_target_total']} "
        f"container-payload-letI={summary['container_payload_letI_total']} "
        f"broad-simp={summary['broad_simp_total']} "
        f"wall={elapsed:.2f}s"
    )
    print("top declaration spans:")
    for row in payload["top_declaration_spans"]:
        print(f"  span={row['span']:4d} {row_label(row)}")
    print("top public signature towers:")
    for row in payload["top_signature_towers"]:
        print(
            f"  letI={row['signature']['letI']:2d} "
            f"bodyLetI={row['body']['letI']:2d} span={row['span']:4d} "
            f"{row_label(row)}"
        )
    print("top duplicated signature/body heavy targets:")
    for row in payload["top_duplicated_towers"]:
        print(
            f"  targets={row['duplicate_heavy_target_count']:2d} "
            f"constructors={row['duplicate_constructor_count']:2d} "
            f"span={row['span']:4d} {row_label(row)}"
        )
    print("top structure/inductive constructor payload towers:")
    for row in payload["top_container_payload_towers"]:
        print(
            f"  letI={row['body']['letI']:2d} "
            f"heavy={sum(row['body_heavy_targets'].values()):2d} "
            f"span={row['span']:4d} {row_label(row)}"
        )
    print("top broad simp declarations:")
    for row in payload["top_broad_simp"]:
        print(
            f"  broad={row['broad_simp']:3d} span={row['span']:4d} "
            f"{row_label(row)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
