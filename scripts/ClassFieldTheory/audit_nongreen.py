#!/usr/bin/env python3
"""Audit the non-green ClassFieldTheory import frontier and elaboration risks.

This is deliberately a read-only audit.  It never invokes Lean or permits a
build action: one Lake ``--no-build`` planner pass validates saved trace hashes.
The report combines that freshness result with the local import graph and
source-shape metrics so that a small frontier file which accidentally pulls in
a large unfinished branch is visible before `lake build` elaborates it.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import sys


SCRIPT_DIR = Path(__file__).resolve().parent
TOOLS_DIR = SCRIPT_DIR.parent
sys.path.insert(0, str(TOOLS_DIR))

from _lean_tool_common import import_modules, repo_root  # noqa: E402
from green_status import (  # noqa: E402
    DEFAULT_LAKE,
    LakeProbeError,
    configured_build_dir,
    source_snapshot,
    source_tree_matches,
    trace_status,
)


ROOT = repo_root()
SOURCE_ROOT = ROOT / "Lean4" / "ClassFieldTheory"
DECLARATION_RE = re.compile(
    r"^\s*(?:(?:@\[[^\]]*\])\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b"
    r"(?:\s+(?P<name>[^\s:{(\[]+))?"
)
LET_I_RE = re.compile(r"\bletI\b")
INFER_INSTANCE_RE = re.compile(r"\binferInstance\b")
SIMP_ONLY_RE = re.compile(
    r"^\s*(?:simpa|simp)(?:_all)?\s+only\b", re.MULTILINE
)
BROAD_SIMP_RE = re.compile(
    r"^\s*(?:simpa|simp)(?:_all)?\b(?!\s+only\b)", re.MULTILINE
)
CHANGE_RE = re.compile(r"\bchange\b")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=configured_build_dir())
    parser.add_argument("--lake", type=Path, default=DEFAULT_LAKE)
    parser.add_argument("--probe-timeout", type=float, default=60.0)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--limit", type=int, default=20)
    return parser.parse_args()


def source_metrics(path: Path) -> dict[str, object]:
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    declarations: list[tuple[int, str]] = []
    for line_number, line in enumerate(lines, 1):
        match = DECLARATION_RE.match(line)
        if match:
            declarations.append((line_number, match.group("name") or "<anonymous>"))
    spans: list[tuple[int, str, int]] = []
    for index, (start, name) in enumerate(declarations):
        end = declarations[index + 1][0] - 1 if index + 1 < len(declarations) else len(lines)
        spans.append((end - start + 1, name, start))
    largest = max(spans, default=(0, "<module>", 1))
    return {
        "lines": len(lines),
        "declarations": len(declarations),
        "max_declaration_lines": largest[0],
        "max_declaration": largest[1],
        "max_declaration_line": largest[2],
        "letI": len(LET_I_RE.findall(text)),
        "inferInstance": len(INFER_INSTANCE_RE.findall(text)),
        "broad_simp": len(BROAD_SIMP_RE.findall(text)),
        "simp_only": len(SIMP_ONLY_RE.findall(text)),
        "change": len(CHANGE_RE.findall(text)),
    }


def main() -> int:
    args = parse_args()
    if args.limit <= 0:
        raise SystemExit("--limit must be positive")
    if args.probe_timeout <= 0:
        raise SystemExit("--probe-timeout must be positive")
    build_dir = args.build_dir.resolve()
    configured = configured_build_dir()
    if build_dir != configured:
        raise SystemExit(
            "--build-dir must match lakefile.toml for authoritative trace "
            f"probing: expected {configured}, got {build_dir}"
        )
    files = sorted(path.resolve() for path in SOURCE_ROOT.rglob("*.lean"))
    source_state = source_snapshot(files)
    file_by_module = {
        path.relative_to(SOURCE_ROOT).with_suffix("").as_posix().replace("/", "."): path
        for path in files
    }
    imports: dict[str, set[str]] = {}
    for module, path in file_by_module.items():
        text = path.read_text(encoding="utf-8", errors="replace")
        imports[module] = {
            imported for imported in import_modules(text) if imported in file_by_module
        }

    try:
        status = trace_status(
            set(file_by_module),
            imports,
            lake=args.lake.resolve(),
            timeout=args.probe_timeout,
        )
    except (LakeProbeError, ValueError) as error:
        print(f"nongreen-audit: freshness probe FAILED: {error}", file=sys.stderr)
        return 2
    green_modules = status.green
    no_green = status.no_green
    frontier_modules = status.frontier

    closure_memo: dict[str, frozenset[str]] = {}

    def import_closure(module: str, active: frozenset[str] = frozenset()) -> frozenset[str]:
        if module in closure_memo:
            return closure_memo[module]
        if module in active:
            return frozenset()
        closure = {module}
        next_active = active | {module}
        for dependency in imports[module]:
            closure.update(import_closure(dependency, next_active))
        result = frozenset(closure)
        closure_memo[module] = result
        return result

    for module in sorted(file_by_module):
        import_closure(module)
    blocking = {
        module: sorted(imports[module] & no_green)
        for module in no_green
    }
    reverse: dict[str, set[str]] = defaultdict(set)
    for module in no_green:
        for dependency in blocking[module]:
            reverse[dependency].add(module)

    dependent_memo: dict[str, set[str]] = {}

    def downstream(module: str, active: set[str] | None = None) -> set[str]:
        if module in dependent_memo:
            return dependent_memo[module]
        active = set() if active is None else active
        if module in active:
            return set()
        next_active = active | {module}
        result: set[str] = set()
        for dependent in reverse[module]:
            result.add(dependent)
            result.update(downstream(dependent, next_active))
        dependent_memo[module] = result
        return result

    layer_memo: dict[str, int | None] = {}

    def layer(module: str, active: set[str] | None = None) -> int | None:
        if module in layer_memo:
            return layer_memo[module]
        active = set() if active is None else active
        if module in active:
            return None
        dependencies = blocking[module]
        if not dependencies:
            result: int | None = 0
        else:
            child_layers = [layer(dependency, active | {module}) for dependency in dependencies]
            result = None if any(value is None for value in child_layers) else 1 + max(
                value for value in child_layers if value is not None
            )
        layer_memo[module] = result
        return result

    metrics_by_module = {
        module: source_metrics(path) for module, path in file_by_module.items()
    }
    if not source_tree_matches(SOURCE_ROOT, files, source_state):
        print(
            "nongreen-audit: FAILED: Lean sources changed during the audit; "
            "retry for a coherent snapshot",
            file=sys.stderr,
        )
        return 2
    library_rows: list[dict[str, object]] = [
        {
            "module": module,
            "path": str(file_by_module[module]),
            "import_closure_modules": len(import_closure(module)),
            "import_closure_lines": sum(
                int(metrics_by_module[dependency]["lines"])
                for dependency in import_closure(module)
            ),
            **metrics_by_module[module],
        }
        for module in sorted(file_by_module)
    ]
    rows: list[dict[str, object]] = []
    for module in sorted(no_green):
        metrics = metrics_by_module[module]
        rows.append({
            "module": module,
            "path": str(file_by_module[module]),
            "layer": layer(module),
            "blocking_imports": blocking[module],
            "blocking_import_count": len(blocking[module]),
            "downstream_no_green": len(downstream(module)),
            "direct_local_imports": len(imports[module]),
            "import_closure_modules": len(import_closure(module)),
            "import_closure_lines": sum(
                int(metrics_by_module[dependency]["lines"])
                for dependency in import_closure(module)
            ),
            **metrics,
        })

    frontier = [row for row in rows if row["module"] in frontier_modules]
    branch_counts = Counter(
        module.split(".")[1] if module.startswith("GlobalClassFieldTheory.") else module.split(".")[0]
        for module in no_green
    )
    payload = {
        "build_dir": str(build_dir),
        "green": len(green_modules),
        "no_green": len(no_green),
        "total": len(file_by_module),
        "frontier": len(frontier),
        "trace_stale_roots": list(status.stale_roots),
        "probe_wall_seconds": round(status.probe_wall_seconds, 3),
        "freshness": "lake_trace_no_build",
        "branch_counts": dict(sorted(branch_counts.items())),
        "totals": {
            "letI": sum(int(row["letI"]) for row in rows),
            "inferInstance": sum(int(row["inferInstance"]) for row in rows),
            "broad_simp": sum(int(row["broad_simp"]) for row in rows),
            "simp_only": sum(int(row["simp_only"]) for row in rows),
            "change": sum(int(row["change"]) for row in rows),
        },
        "library_totals": {
            "lines": sum(int(row["lines"]) for row in library_rows),
            "declarations": sum(int(row["declarations"]) for row in library_rows),
            "letI": sum(int(row["letI"]) for row in library_rows),
            "inferInstance": sum(int(row["inferInstance"]) for row in library_rows),
            "broad_simp": sum(int(row["broad_simp"]) for row in library_rows),
            "simp_only": sum(int(row["simp_only"]) for row in library_rows),
            "change": sum(int(row["change"]) for row in library_rows),
        },
        "library_top_declaration_spans": sorted(
            library_rows,
            key=lambda row: (-row["max_declaration_lines"], row["module"]),
        )[: args.limit],
        "library_top_instance_density": sorted(
            library_rows,
            key=lambda row: (
                -(row["letI"] + row["inferInstance"]),
                -row["max_declaration_lines"],
                row["module"],
            ),
        )[: args.limit],
        "library_top_broad_simp": sorted(
            library_rows,
            key=lambda row: (-row["broad_simp"], -row["lines"], row["module"]),
        )[: args.limit],
        "library_top_import_closure": sorted(
            library_rows,
            key=lambda row: (
                -row["import_closure_modules"],
                -row["import_closure_lines"],
                row["module"],
            ),
        )[: args.limit],
        "frontier_rows": sorted(frontier, key=lambda row: (row["lines"], row["module"])),
        "top_downstream_impact": sorted(
            rows, key=lambda row: (-row["downstream_no_green"], row["module"])
        )[: args.limit],
        "top_declaration_spans": sorted(
            rows, key=lambda row: (-row["max_declaration_lines"], row["module"])
        )[: args.limit],
        "top_instance_density": sorted(
            rows,
            key=lambda row: (
                -(row["letI"] + row["inferInstance"]),
                -row["max_declaration_lines"],
                row["module"],
            ),
        )[: args.limit],
        "top_broad_simp": sorted(
            rows,
            key=lambda row: (-row["broad_simp"], -row["lines"], row["module"]),
        )[: args.limit],
        "blocking_edges": [
            {
                "module": row["module"],
                "lines": row["lines"],
                "blocking_import": dependency,
                "dependency_lines": metrics_by_module[dependency]["lines"],
                "dependency_downstream_no_green": len(downstream(dependency)),
            }
            for row in rows
            for dependency in row["blocking_imports"]
        ],
        "modules": rows,
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0

    print(
        f"nongreen-audit: green={payload['green']}/{payload['total']} "
        f"no_green={payload['no_green']} frontier={payload['frontier']}"
    )
    print("branches: " + ", ".join(f"{name}={count}" for name, count in branch_counts.items()))
    print(
        "source totals: "
        + ", ".join(f"{name}={count}" for name, count in payload["totals"].items())
    )
    print(
        "library source totals: "
        + ", ".join(
            f"{name}={count}" for name, count in payload["library_totals"].items()
        )
    )
    print("frontier:")
    for row in payload["frontier_rows"]:
        print(
            f"  {row['lines']:5d} lines  span={row['max_declaration_lines']:4d} "
            f"letI={row['letI']:2d} closure={row['import_closure_modules']:4d} "
            f"impact={row['downstream_no_green']:2d}  {row['module']}"
        )
    print("top declaration spans:")
    for row in payload["top_declaration_spans"]:
        print(
            f"  {row['max_declaration_lines']:4d} lines at {row['max_declaration_line']:4d} "
            f"letI={row['letI']:2d} infer={row['inferInstance']:2d} "
            f"{row['module']}::{row['max_declaration']}"
        )
    print("top downstream impact:")
    for row in payload["top_downstream_impact"]:
        print(
            f"  impact={row['downstream_no_green']:2d} layer={row['layer']} "
            f"blockers={row['blocking_import_count']:2d} {row['module']}"
        )
    print("library top declaration spans:")
    for row in payload["library_top_declaration_spans"]:
        print(
            f"  {row['max_declaration_lines']:4d} lines at {row['max_declaration_line']:4d} "
            f"letI={row['letI']:3d} infer={row['inferInstance']:2d} "
            f"{row['module']}::{row['max_declaration']}"
        )
    print("library top import closures:")
    for row in payload["library_top_import_closure"]:
        print(
            f"  modules={row['import_closure_modules']:4d} "
            f"lines={row['import_closure_lines']:6d} {row['module']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
