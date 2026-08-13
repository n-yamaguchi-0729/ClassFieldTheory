#!/usr/bin/env python3
"""Measure reproducible build and elaboration hotspots for the public roots.

Incremental measurements use the current workspace.  A clean measurement is
performed in a disposable package copy whose `.lake/packages` is a read-only
symlink to the current dependency checkout; it never deletes or moves the
workspace build directory.  Wall-clock and peak RSS measurements are facts for
one machine, not CI pass/fail thresholds.  Static complexity and import-closure
ceilings are enforced separately by `check_architecture_contract.py`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

from source_layout import (
    CANONICAL_ROOT,
    DOCS_ROOT,
    LEAN_ROOT,
    WORKSPACE_ROOT,
    contract_source_files,
    lean_code_line_count,
    lean_source_files,
    module_source_entries,
    normalized_lean_code,
    source_code_sha256,
    source_inventory,
    source_relative_path,
    strip_lean_comments,
)


LIBRARY_ROOT = LEAN_ROOT
DEFAULT_OUTPUT = DOCS_ROOT / "performance-baseline.json"
SCHEMA_VERSION = 2

BENCHMARK_ROOTS = (
    "ClassFieldTheory",
    "ValuationTheory",
    "LocalFieldTheory",
    "LubinTate",
    "RamificationTheory",
    "CyclicCohomology",
    "KummerTheory",
    "AbstractClassFieldTheory",
    "AlgebraicNumberTheory",
    "LocalClassFieldTheory.Concrete",
    "LocalClassFieldTheory.Concrete.LubinTateApplication",
    "LocalClassFieldTheory",
    "LocalClassFieldTheory.Concrete.Finite.LocalReciprocity",
    "LocalClassFieldTheory.Concrete.Finite.Existence",
    "LocalClassFieldTheory.Concrete.Finite.Conductor",
    "LocalClassFieldTheory.Concrete.Finite.UnramifiedConductor",
    "LocalClassFieldTheory.Concrete.Infinite",
    "LocalClassFieldTheory.Concrete.Kummer",
    "HasseArf",
    "KroneckerWeber",
)

PUBLIC_CLEAN_ROOTS = (
    "ClassFieldTheory",
    "LocalClassFieldTheory",
    "LocalClassFieldTheory.Concrete.Finite.LocalReciprocity",
    "LocalClassFieldTheory.Concrete.Finite.Existence",
    "LocalClassFieldTheory.Concrete.Finite.Conductor",
    "LocalClassFieldTheory.Concrete.Finite.UnramifiedConductor",
    "LocalClassFieldTheory.Concrete.Infinite",
    "LocalClassFieldTheory.Concrete.Kummer",
    "LocalClassFieldTheory.Concrete.LubinTateApplication",
    "HasseArf",
    "KroneckerWeber",
)

DECLARATION_RE = re.compile(
    r"^\s*(?:(?:@\[[^\]]*\])\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b"
    r"(?:\s+(?P<name>[^\s:{(\[]+))?"
)
TIME_EVENT_RE = re.compile(
    r"(?P<event>[^\n]+?) took (?P<value>[0-9]+(?:\.[0-9]+)?)(?P<unit>ms|s)"
)


def run_timed(command: list[str], cwd: Path) -> dict[str, object]:
    """Run a command under GNU time and retain a bounded failure log."""

    with tempfile.NamedTemporaryFile(prefix="cft-time-", delete=False) as timing:
        timing_path = Path(timing.name)
    try:
        completed = subprocess.run(
            [
                "/usr/bin/time",
                "-f",
                "%e\t%M\t%U\t%S",
                "-o",
                str(timing_path),
                *command,
            ],
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        fields = timing_path.read_text(encoding="utf-8").strip().split("\t")
        measurement: dict[str, object] = {
            "returncode": completed.returncode,
            "command": command,
        }
        if len(fields) == 4:
            measurement.update(
                {
                    "wall_seconds": float(fields[0]),
                    "peak_rss_kib": int(fields[1]),
                    "user_seconds": float(fields[2]),
                    "system_seconds": float(fields[3]),
                }
            )
        if completed.returncode != 0:
            measurement["failure_log_tail"] = completed.stdout.splitlines()[-80:]
        return measurement
    finally:
        timing_path.unlink(missing_ok=True)


def incremental_builds(roots: list[str]) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    for root in roots:
        print(f"performance: incremental {root}", flush=True)
        measurement = run_timed(["lake", "build", root], WORKSPACE_ROOT)
        measurement["root"] = root
        results.append(measurement)
        if measurement["returncode"] != 0:
            break
    return results


def prepare_disposable_workspace(destination: Path) -> None:
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        source = WORKSPACE_ROOT / name
        if source.exists():
            shutil.copy2(source, destination / name)
    target_tree = destination / "Lean4" / "ClassFieldTheory"
    target_tree.mkdir(parents=True)
    for source in module_source_entries():
        target = target_tree / source.name
        if source.is_dir():
            shutil.copytree(source, target)
        else:
            shutil.copy2(source, target)
    shutil.copy2(
        CANONICAL_ROOT,
        target_tree / "ClassFieldTheory.lean",
    )
    lake_dir = destination / ".lake"
    lake_dir.mkdir()
    dependencies = WORKSPACE_ROOT / ".lake" / "packages"
    if not dependencies.is_dir():
        raise RuntimeError(f"dependency checkout is missing: {dependencies}")
    (lake_dir / "packages").symlink_to(dependencies, target_is_directory=True)


def clean_build(root: str) -> dict[str, object]:
    print(f"performance: clean disposable build {root}", flush=True)
    with tempfile.TemporaryDirectory(prefix="cft-clean-") as temporary:
        isolated = Path(temporary)
        prepare_disposable_workspace(isolated)
        measurement = run_timed(["lake", "--no-cache", "build", root], isolated)
        measurement["root"] = root
        measurement["workspace_kind"] = "disposable_source_copy"
        return measurement


def source_declarations(path: Path) -> list[tuple[int, str]]:
    declarations: list[tuple[int, str]] = []
    source = path.read_text(encoding="utf-8", errors="replace")
    for line_number, line in enumerate(strip_lean_comments(source).splitlines(), 1):
        match = DECLARATION_RE.match(line)
        if not match:
            continue
        declarations.append((line_number, match.group("name") or "<anonymous instance>"))
    return declarations


def declaration_at(declarations: list[tuple[int, str]], line: int) -> str:
    current = "<module command>"
    for declaration_line, name in declarations:
        if declaration_line > line:
            break
        current = name
    return current


def code_line_numbers(source: str) -> list[int]:
    """Map every physical source line to its stable code-only line ordinal."""

    result: list[int] = []
    code_line = 0
    for line in strip_lean_comments(source).splitlines():
        if line.strip():
            code_line += 1
        result.append(code_line)
    return result


def largest_sources(limit: int) -> list[Path]:
    ranked = sorted(
        lean_source_files(),
        key=lambda path: (
            -lean_code_line_count(
                path.read_text(encoding="utf-8", errors="replace")
            ),
            source_relative_path(path),
        ),
    )
    return ranked[:limit]


def profile_sources(paths: list[Path], threshold_ms: int) -> dict[str, object]:
    events: list[dict[str, object]] = []
    failures: list[dict[str, object]] = []
    for path in paths:
        relative = path.relative_to(WORKSPACE_ROOT)
        print(f"performance: profile {relative}", flush=True)
        completed = subprocess.run(
            [
                "lake",
                "env",
                "lean",
                "--json",
                "--profile",
                f"-Dprofiler.threshold={threshold_ms}",
                str(relative),
            ],
            cwd=WORKSPACE_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0:
            failures.append(
                {
                    "file": path.relative_to(LIBRARY_ROOT).as_posix(),
                    "returncode": completed.returncode,
                    "stderr_tail": completed.stderr.splitlines()[-40:],
                }
            )
            continue
        source = path.read_text(encoding="utf-8", errors="replace")
        declarations = source_declarations(path)
        stable_lines = code_line_numbers(source)
        for raw_line in completed.stdout.splitlines():
            try:
                message = json.loads(raw_line)
            except json.JSONDecodeError:
                continue
            position = message.get("pos")
            if not isinstance(position, dict) or not isinstance(position.get("line"), int):
                continue
            line_number = int(position["line"])
            data = str(message.get("data", ""))
            for match in TIME_EVENT_RE.finditer(data):
                milliseconds = float(match.group("value"))
                if match.group("unit") == "s":
                    milliseconds *= 1000
                stable_line = (
                    stable_lines[min(line_number, len(stable_lines)) - 1]
                    if stable_lines and line_number > 0
                    else 0
                )
                events.append(
                    {
                        "milliseconds": round(milliseconds, 3),
                        "event": match.group("event"),
                        "declaration": declaration_at(declarations, line_number),
                        "file": path.relative_to(LIBRARY_ROOT).as_posix(),
                        "code_line": stable_line,
                    }
                )
    events.sort(key=lambda item: float(item["milliseconds"]), reverse=True)
    typeclass = [item for item in events if str(item["event"]).startswith("typeclass inference")]
    elaboration = [item for item in events if item["event"] == "elaboration"]
    return {
        "threshold_ms": threshold_ms,
        "profiled_files": [path.relative_to(LIBRARY_ROOT).as_posix() for path in paths],
        "top_20_events": events[:20],
        "top_20_elaboration": elaboration[:20],
        "top_20_typeclass_inference": typeclass[:20],
        "failures": failures,
    }


def let_i_hotspots() -> list[dict[str, object]]:
    counts: list[tuple[int, Path]] = []
    pattern = re.compile(r"\bletI\b")
    for path in lean_source_files():
        count = len(
            pattern.findall(
                normalized_lean_code(
                    path.read_text(encoding="utf-8", errors="replace")
                )
            )
        )
        if count:
            counts.append((count, path))
    return [
        {"count": count, "file": path.relative_to(LIBRARY_ROOT).as_posix()}
        for count, path in sorted(counts, reverse=True)[:20]
    ]


def source_sha256() -> str:
    digest = hashlib.sha256()
    for path in contract_source_files():
        digest.update(source_relative_path(path).encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def command_version(command: list[str]) -> str:
    completed = subprocess.run(
        command,
        cwd=WORKSPACE_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.stdout.strip().splitlines()[0] if completed.stdout.strip() else "unknown"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--full-baseline",
        action="store_true",
        help=(
            "official complete refresh: replace the record, measure every "
            "incremental and reviewed clean root, and profile twenty code-largest files"
        ),
    )
    parser.add_argument(
        "--incremental-root",
        action="append",
        default=[],
        help="measure an existing-workspace build; repeatable (default: all benchmark roots)",
    )
    parser.add_argument(
        "--skip-incremental",
        action="store_true",
        help="do not measure incremental builds",
    )
    parser.add_argument(
        "--clean-root",
        action="append",
        default=[],
        help="measure a root in a fresh disposable source/build tree; repeatable",
    )
    parser.add_argument(
        "--profile-hotspots",
        action="store_true",
        help="re-elaborate the largest source files with the Lean profiler",
    )
    parser.add_argument("--profile-file-count", type=int, default=20)
    parser.add_argument("--profile-threshold-ms", type=int, default=25)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--replace",
        action="store_true",
        help="discard existing measurements instead of updating requested sections",
    )
    args = parser.parse_args()

    if args.full_baseline and (
        args.incremental_root
        or args.skip_incremental
        or args.clean_root
        or args.profile_hotspots
        or args.replace
    ):
        parser.error(
            "--full-baseline cannot be combined with partial-selection or --replace options"
        )
    if shutil.which("lake") is None:
        parser.error("lake is not available on PATH")
    if not Path("/usr/bin/time").is_file():
        parser.error("GNU /usr/bin/time is required")

    if args.full_baseline:
        args.replace = True
        args.profile_hotspots = True
        args.profile_file_count = 20
        requested_incremental = list(BENCHMARK_ROOTS)
        requested_clean = list(PUBLIC_CLEAN_ROOTS)
    else:
        requested_incremental = args.incremental_root or list(BENCHMARK_ROOTS)
        requested_clean = list(args.clean_root)
    unknown = (set(requested_incremental) | set(requested_clean)) - set(BENCHMARK_ROOTS)
    if unknown:
        parser.error("unknown benchmark roots: " + ", ".join(sorted(unknown)))

    payload: dict[str, object] = {}
    initial_inventory = source_inventory()
    current_code_sha256 = source_code_sha256()
    if args.output.exists() and not args.replace:
        try:
            existing = json.loads(args.output.read_text(encoding="utf-8"))
            if (
                isinstance(existing, dict)
                and existing.get("schema_version") == SCHEMA_VERSION
            ):
                payload.update(existing)
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            parser.error(f"cannot update malformed performance record: {error}")
        if not payload:
            parser.error(
                "a complete schema-2 record is required for partial updates; "
                "run with --full-baseline"
            )
        if payload.get("source_code_sha256") != current_code_sha256:
            parser.error(
                "Lean code changed since the recorded measurements; "
                "run with --full-baseline"
            )
    payload.update({
        "schema_version": SCHEMA_VERSION,
        "source_inventory": initial_inventory,
        "source_code_sha256": current_code_sha256,
        "source_sha256": source_sha256(),
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "cpu_count": os.cpu_count(),
            "python": platform.python_version(),
            "lean": command_version(["lake", "env", "lean", "--version"]),
            "lake": command_version(["lake", "--version"]),
        },
        "measurement_policy": {
            "wall_time_is_advisory": True,
            "clean_build_never_mutates_workspace_artifacts": True,
            "source_freshness_ignores_comments_and_blank_lines": True,
            "peak_rss_unit": "KiB",
        },
        "measurement_scope": {
            "incremental_roots": list(BENCHMARK_ROOTS),
            "clean_roots": list(PUBLIC_CLEAN_ROOTS),
            "profile_file_count": 20,
            "largest_file_metric": "nonblank code lines after removing Lean comments",
        },
        "letI_hotspots": let_i_hotspots(),
    })
    if not args.skip_incremental:
        old_incremental = payload.get("incremental_builds", [])
        by_root = {
            str(item.get("root")): item
            for item in old_incremental
            if isinstance(item, dict) and item.get("root")
        }
        for item in incremental_builds(requested_incremental):
            by_root[str(item["root"])] = item
        payload["incremental_builds"] = [by_root[root] for root in sorted(by_root)]
        if any(
            isinstance(item, dict) and item.get("returncode") != 0
            for item in payload["incremental_builds"]
        ):
            print(
                "performance: incremental measurement failed; "
                "the baseline was not replaced",
                file=sys.stderr,
            )
            return 1
    if requested_clean:
        old_clean = payload.get("clean_builds", [])
        by_root = {
            str(item.get("root")): item
            for item in old_clean
            if isinstance(item, dict) and item.get("root")
        }
        for root in requested_clean:
            by_root[root] = clean_build(root)
        payload["clean_builds"] = [by_root[root] for root in sorted(by_root)]
        if any(
            isinstance(item, dict) and item.get("returncode") != 0
            for item in payload["clean_builds"]
        ):
            print(
                "performance: clean measurement failed; "
                "the baseline was not replaced",
                file=sys.stderr,
            )
            return 1
    if args.profile_hotspots:
        payload["profiler"] = profile_sources(
            largest_sources(args.profile_file_count), args.profile_threshold_ms
        )
        profiler = payload["profiler"]
        if (
            isinstance(profiler, dict)
            and profiler.get("failures")
        ):
            print(
                "performance: profiler elaboration failed; "
                "the baseline was not replaced",
                file=sys.stderr,
            )
            return 1

    if (
        source_inventory() != initial_inventory
        or source_code_sha256() != current_code_sha256
    ):
        print(
            "performance: Lean source/module set changed during measurement; "
            "discarding the run without replacing the baseline",
            file=sys.stderr,
        )
        return 1

    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary_output = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary_output.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    temporary_output.replace(args.output)
    print(f"performance: wrote {args.output}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
