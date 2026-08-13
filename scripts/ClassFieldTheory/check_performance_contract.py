#!/usr/bin/env python3
"""Validate completeness and freshness of the advisory performance record."""

from __future__ import annotations

import argparse
from datetime import datetime
import json
import math
from pathlib import Path
import re
import sys

from audit_declaration_towers import (
    CONTRACT_CEILING_KEYS,
    SCHEMA_VERSION as STATIC_SCHEMA_VERSION,
    audit_sources,
    compact_contract,
)
from measure_performance import (
    BENCHMARK_ROOTS,
    DEFAULT_OUTPUT,
    PUBLIC_CLEAN_ROOTS,
    SCHEMA_VERSION,
    code_line_numbers,
    largest_sources,
    let_i_hotspots,
)
from source_layout import (
    DOCS_ROOT,
    LEAN_ROOT,
    source_code_sha256,
    source_inventory,
)


DEFAULT_STATIC_BASELINE = DOCS_ROOT / "declaration-performance-contract.json"


EXPECTED_POLICY = {
    "wall_time_is_advisory": True,
    "clean_build_never_mutates_workspace_artifacts": True,
    "source_freshness_ignores_comments_and_blank_lines": True,
    "peak_rss_unit": "KiB",
}
EXPECTED_SCOPE = {
    "incremental_roots": list(BENCHMARK_ROOTS),
    "clean_roots": list(PUBLIC_CLEAN_ROOTS),
    "profile_file_count": 20,
    "largest_file_metric": "nonblank code lines after removing Lean comments",
}


def finite_nonnegative_number(value: object) -> bool:
    return (
        not isinstance(value, bool)
        and isinstance(value, (int, float))
        and math.isfinite(float(value))
        and value >= 0
    )


def validate_static_performance_contract(
    baseline: object,
    current: dict[str, object],
) -> list[str]:
    """Validate the source-only declaration-risk ceilings.

    This record is intentionally independent of the machine-specific build
    measurements below.  Improvements are accepted; any increase above a
    reviewed ceiling requires an explicit baseline review.
    """

    errors: list[str] = []
    if not isinstance(baseline, dict):
        return ["static performance baseline root must be an object"]
    if baseline.get("schema_version") != STATIC_SCHEMA_VERSION:
        errors.append(
            "static performance baseline schema_version must be "
            f"{STATIC_SCHEMA_VERSION}"
        )
    inventory = current.get("source_inventory")
    if not isinstance(inventory, dict):
        errors.append("current static source inventory is missing")
    else:
        expected_inventory = {
            "module_count": inventory.get("module_count"),
            "modules_sha256": inventory.get("modules_sha256"),
        }
        if baseline.get("source_inventory") != expected_inventory:
            errors.append(
                "static performance source inventory differs from the current "
                "Class Field Theory module set"
            )
    ceilings = baseline.get("ceilings")
    summary = current.get("summary")
    if not isinstance(ceilings, dict):
        errors.append("static performance ceilings must be an object")
        return errors
    if set(ceilings) != set(CONTRACT_CEILING_KEYS):
        missing = sorted(set(CONTRACT_CEILING_KEYS) - set(ceilings))
        stale = sorted(set(ceilings) - set(CONTRACT_CEILING_KEYS))
        if missing:
            errors.append(f"static performance ceilings are missing: {missing!r}")
        if stale:
            errors.append(f"static performance ceilings are stale: {stale!r}")
        return errors
    if not isinstance(summary, dict):
        errors.append("current static performance summary is missing")
        return errors
    for key in CONTRACT_CEILING_KEYS:
        value = summary.get(key)
        ceiling = ceilings.get(key)
        if (
            isinstance(value, bool)
            or not isinstance(value, int)
            or isinstance(ceiling, bool)
            or not isinstance(ceiling, int)
            or ceiling < value
        ):
            errors.append(
                f"static performance {key} is {value!r}, above or "
                f"incompatible with ceiling {ceiling!r}"
            )
    report = baseline.get("current_report")
    if not isinstance(report, dict) or set(report) != set(CONTRACT_CEILING_KEYS):
        errors.append(
            "static performance current_report must record every ceiling metric"
        )
    hotspots = baseline.get("hotspots")
    if not isinstance(hotspots, dict) or set(hotspots) != {
        "declaration_spans",
        "signature_towers",
        "duplicated_towers",
        "container_payload_towers",
        "broad_simp",
    }:
        errors.append("static performance hotspot report is incomplete")
    return errors


def read_static_baseline(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_measurements(
    entries: object,
    expected_roots: tuple[str, ...],
    label: str,
    errors: list[str],
    *,
    clean: bool,
) -> None:
    """Validate one exact benchmark-root inventory and its measurements."""

    if not isinstance(entries, list):
        errors.append(f"{label} must be an array")
        return
    by_root: dict[str, dict[str, object]] = {}
    for index, entry in enumerate(entries):
        item_label = f"{label}[{index}]"
        if not isinstance(entry, dict):
            errors.append(f"{item_label} must be an object")
            continue
        root = entry.get("root")
        if not isinstance(root, str) or not root:
            errors.append(f"{item_label}.root must be nonempty")
            continue
        if root in by_root:
            errors.append(f"{label} has duplicate root {root}")
        by_root[root] = entry
        if entry.get("returncode") != 0:
            errors.append(f"{label} root {root} did not build successfully")
        expected_command = (
            ["lake", "--no-cache", "build", root]
            if clean
            else ["lake", "build", root]
        )
        if entry.get("command") != expected_command:
            errors.append(
                f"{label} root {root} has unexpected command "
                f"{entry.get('command')!r}"
            )
        for field in (
            "wall_seconds",
            "peak_rss_kib",
            "user_seconds",
            "system_seconds",
        ):
            if not finite_nonnegative_number(entry.get(field)):
                errors.append(f"{label} root {root} has invalid {field}")
        if clean:
            if entry.get("workspace_kind") != "disposable_source_copy":
                errors.append(
                    f"{label} root {root} was not measured in a disposable copy"
                )
        elif "workspace_kind" in entry:
            errors.append(
                f"{label} root {root} unexpectedly claims a clean workspace"
            )
    missing = set(expected_roots) - set(by_root)
    extra = set(by_root) - set(expected_roots)
    if missing:
        errors.append(f"{label} is missing roots: {', '.join(sorted(missing))}")
    if extra:
        errors.append(f"{label} has unknown roots: {', '.join(sorted(extra))}")


def validate_profiler(payload: object, errors: list[str]) -> None:
    if not isinstance(payload, dict):
        errors.append("profiler record is missing")
        return
    if (
        isinstance(payload.get("threshold_ms"), bool)
        or not isinstance(payload.get("threshold_ms"), int)
        or int(payload["threshold_ms"]) <= 0
    ):
        errors.append("profiler.threshold_ms must be a positive integer")
    if payload.get("failures") != []:
        errors.append("one or more profiler source elaborations failed")

    expected_files = [
        path.relative_to(LEAN_ROOT).as_posix() for path in largest_sources(20)
    ]
    if payload.get("profiled_files") != expected_files:
        errors.append(
            "profiled_files is not the current twenty code-largest Lean sources"
        )
    expected_file_set = set(expected_files)
    for field in (
        "top_20_events",
        "top_20_elaboration",
        "top_20_typeclass_inference",
    ):
        entries = payload.get(field)
        if not isinstance(entries, list) or not entries:
            errors.append(f"profiler field {field} is missing or empty")
            continue
        if len(entries) > 20:
            errors.append(f"profiler field {field} contains more than twenty entries")
        previous = math.inf
        for index, entry in enumerate(entries):
            label = f"profiler.{field}[{index}]"
            if not isinstance(entry, dict):
                errors.append(f"{label} must be an object")
                continue
            milliseconds = entry.get("milliseconds")
            if not finite_nonnegative_number(milliseconds):
                errors.append(f"{label}.milliseconds is invalid")
            elif float(milliseconds) > previous:
                errors.append(f"profiler field {field} is not slowest-first")
            else:
                previous = float(milliseconds)
            if entry.get("file") not in expected_file_set:
                errors.append(f"{label}.file is outside profiled_files")
            if (
                isinstance(entry.get("code_line"), bool)
                or not isinstance(entry.get("code_line"), int)
                or int(entry["code_line"]) <= 0
            ):
                errors.append(f"{label}.code_line must be positive")
            if not isinstance(entry.get("event"), str) or not entry.get("event"):
                errors.append(f"{label}.event must be nonempty")
            if (
                not isinstance(entry.get("declaration"), str)
                or not entry.get("declaration")
            ):
                errors.append(f"{label}.declaration must be nonempty")
            event = str(entry.get("event", ""))
            if field == "top_20_elaboration" and event != "elaboration":
                errors.append(f"{label} is not an elaboration event")
            if (
                field == "top_20_typeclass_inference"
                and not event.startswith("typeclass inference")
            ):
                errors.append(f"{label} is not a typeclass-inference event")


def validate_payload(payload: object) -> list[str]:
    errors: list[str] = []
    if not isinstance(payload, dict):
        return ["performance record root must be an object"]
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version must be {SCHEMA_VERSION}")
    if payload.get("source_inventory") != source_inventory():
        errors.append(
            "source_inventory differs from the current Class Field "
            "Theory module set"
        )
    if payload.get("source_code_sha256") != source_code_sha256():
        errors.append(
            "performance record is stale for current Lean code "
            "(comments and blank lines are ignored)"
        )
    raw_sha = payload.get("source_sha256")
    if not isinstance(raw_sha, str) or not re.fullmatch(r"[0-9a-f]{64}", raw_sha):
        errors.append("source_sha256 must be a lowercase SHA-256 digest")

    recorded_at = payload.get("recorded_at_utc")
    try:
        parsed_time = datetime.fromisoformat(str(recorded_at))
        if parsed_time.tzinfo is None:
            raise ValueError("timezone is missing")
    except ValueError:
        errors.append("recorded_at_utc must be an ISO timestamp with timezone")

    environment = payload.get("environment")
    if not isinstance(environment, dict):
        errors.append("environment must be an object")
    else:
        for field in ("platform", "machine", "python", "lean", "lake"):
            if not isinstance(environment.get(field), str) or not environment.get(field):
                errors.append(f"environment.{field} must be nonempty")
        cpu_count = environment.get("cpu_count")
        if (
            isinstance(cpu_count, bool)
            or not isinstance(cpu_count, int)
            or cpu_count <= 0
        ):
            errors.append("environment.cpu_count must be positive")

    if payload.get("measurement_policy") != EXPECTED_POLICY:
        errors.append("measurement_policy differs from the checker contract")
    if payload.get("measurement_scope") != EXPECTED_SCOPE:
        errors.append("measurement_scope differs from the exact benchmark target set")

    validate_measurements(
        payload.get("incremental_builds"),
        BENCHMARK_ROOTS,
        "incremental_builds",
        errors,
        clean=False,
    )
    validate_measurements(
        payload.get("clean_builds"),
        PUBLIC_CLEAN_ROOTS,
        "clean_builds",
        errors,
        clean=True,
    )
    validate_profiler(payload.get("profiler"), errors)

    if payload.get("letI_hotspots") != let_i_hotspots():
        errors.append("letI hotspot record is stale")
    return errors


def run_self_tests() -> None:
    assert code_line_numbers("/- docs -/\ndef x := 1\n\n-- docs\ntheorem y := rfl") == [
        0,
        1,
        1,
        1,
        2,
    ]
    incremental = {
        "root": "Example",
        "returncode": 0,
        "command": ["lake", "build", "Example"],
        "wall_seconds": 1.0,
        "peak_rss_kib": 1,
        "user_seconds": 0.5,
        "system_seconds": 0.1,
    }
    errors: list[str] = []
    validate_measurements(
        [incremental], ("Example",), "example", errors, clean=False
    )
    assert not errors, errors
    malformed = dict(incremental, peak_rss_kib=-1, command=["true"])
    malformed_errors: list[str] = []
    validate_measurements(
        [malformed], ("Example",), "example", malformed_errors, clean=False
    )
    assert len(malformed_errors) == 2, malformed_errors
    duplicate_errors: list[str] = []
    validate_measurements(
        [incremental, incremental],
        ("Example",),
        "example",
        duplicate_errors,
        clean=False,
    )
    assert any("duplicate root" in error for error in duplicate_errors)

    inventory = {"module_count": 1, "modules_sha256": "0" * 64}
    current = {
        "source_inventory": inventory,
        "summary": {key: 1 for key in CONTRACT_CEILING_KEYS},
    }
    static_baseline = {
        "schema_version": STATIC_SCHEMA_VERSION,
        "source_inventory": inventory,
        "ceilings": {key: 1 for key in CONTRACT_CEILING_KEYS},
        "current_report": {key: 1 for key in CONTRACT_CEILING_KEYS},
        "hotspots": {
            "declaration_spans": [],
            "signature_towers": [],
            "duplicated_towers": [],
            "container_payload_towers": [],
            "broad_simp": [],
        },
    }
    assert not validate_static_performance_contract(static_baseline, current)
    improved = {
        **current,
        "summary": {key: 0 for key in CONTRACT_CEILING_KEYS},
    }
    assert not validate_static_performance_contract(static_baseline, improved)
    regressed = {
        **current,
        "summary": {
            **current["summary"],
            "broad_simp_total": 2,
        },
    }
    regression_errors = validate_static_performance_contract(
        static_baseline, regressed
    )
    assert any("broad_simp_total" in error for error in regression_errors)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run deterministic schema tests without reading the baseline",
    )
    parser.add_argument(
        "--static-only",
        action="store_true",
        help="validate declaration-risk ceilings without build measurements",
    )
    parser.add_argument(
        "--static-baseline",
        type=Path,
        default=DEFAULT_STATIC_BASELINE,
    )
    parser.add_argument(
        "--print-static-report",
        action="store_true",
        help="print the current compact declaration-risk report as JSON",
    )
    args = parser.parse_args()
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(
                f"performance-contract self-test: FAILED: {error}",
                file=sys.stderr,
            )
            return 1
        print("performance-contract self-test: OK")
        return 0

    static_payload = audit_sources(limit=10)
    if args.print_static_report:
        print(
            json.dumps(
                compact_contract(static_payload),
                ensure_ascii=False,
                indent=2,
            )
        )
    try:
        static_baseline = read_static_baseline(args.static_baseline)
    except FileNotFoundError:
        static_errors = [
            f"static performance baseline is missing: {args.static_baseline}"
        ]
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        static_errors = [
            f"cannot read static performance baseline {args.static_baseline}: "
            f"{error}"
        ]
    else:
        static_errors = validate_static_performance_contract(
            static_baseline, static_payload
        )
    if static_errors:
        for error in static_errors:
            print(f"performance-contract: {error}", file=sys.stderr)
        print(
            "performance-contract: FAILED "
            f"({len(static_errors)} static diagnostics)",
            file=sys.stderr,
        )
        return 1
    static_summary = static_payload["summary"]
    assert isinstance(static_summary, dict)
    if args.static_only:
        print(
            "performance-contract: static OK "
            f"({static_summary['files']} modules, "
            f"signature letI={static_summary['public_signature_letI_total']}, "
            f"duplicate targets="
            f"{static_summary['signature_body_duplicate_target_total']}, "
            f"container payload letI="
            f"{static_summary['container_payload_letI_total']}, "
            f"broad simp={static_summary['broad_simp_total']})"
        )
        return 0

    try:
        payload = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(
            f"performance-contract: baseline is missing: {DEFAULT_OUTPUT}; "
            "run measure_performance.py --full-baseline",
            file=sys.stderr,
        )
        return 1
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(
            f"performance-contract: cannot read {DEFAULT_OUTPUT}: {error}",
            file=sys.stderr,
        )
        return 1

    errors = validate_payload(payload)
    if errors:
        for error in errors:
            print(f"performance-contract: {error}", file=sys.stderr)
        print(
            f"performance-contract: FAILED ({len(errors)} diagnostics)",
            file=sys.stderr,
        )
        return 1
    print(
        "performance-contract: OK "
        f"({len(BENCHMARK_ROOTS)} incremental roots, "
        f"{len(PUBLIC_CLEAN_ROOTS)} clean roots, 20 profiled modules)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
