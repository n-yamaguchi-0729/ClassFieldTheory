#!/usr/bin/env python3
"""Report Lake-trace-fresh Lean modules without running build actions.

The authoritative probe is one ordinary ``lake --no-build build`` planner run
over every local module's ``olean`` facet.  Lake compares each saved trace's
input hash with the current dependency trace; artifact mtimes are deliberately
not reimplemented here.  The planner reports the minimal out-of-date roots,
and the local reverse-import closure determines every downstream no-green
module.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from collections.abc import Collection, Mapping
from dataclasses import dataclass
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import tomllib


SCRIPT_DIR = Path(__file__).resolve().parent
TOOLS_DIR = SCRIPT_DIR.parent
sys.path.insert(0, str(TOOLS_DIR))

from _lean_tool_common import import_modules, repo_root  # noqa: E402


ROOT = repo_root()
SOURCE_ROOT = ROOT / "Lean4" / "ClassFieldTheory"
DEFAULT_LAKE = Path(shutil.which("lake") or "lake")
OUT_OF_DATE_ERROR = "error: target is out-of-date and needs to be rebuilt"
BUILDING_RE = re.compile(r"\bBuilding\s+(?P<module>[^\s]+)\s*$")
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


@dataclass(frozen=True)
class TraceStatus:
    green: frozenset[str]
    no_green: frozenset[str]
    frontier: tuple[str, ...]
    stale_roots: tuple[str, ...]
    probe_wall_seconds: float


class LakeProbeError(RuntimeError):
    """The no-build planner could not produce an authoritative status."""


def configured_build_dir() -> Path:
    config = ROOT / "lakefile.toml"
    if config.is_file():
        data = tomllib.loads(config.read_text(encoding="utf-8"))
        raw = data.get("buildDir")
        if isinstance(raw, str) and raw:
            return (ROOT / raw / "lib" / "lean").resolve()
    return (ROOT / ".lake" / "build" / "lib" / "lean").resolve()


def source_snapshot(paths: Collection[Path]) -> tuple[tuple[str, int, int], ...]:
    """Capture enough source metadata to detect an overlapping edit."""

    entries: list[tuple[str, int, int]] = []
    for path in sorted(paths):
        try:
            stat = path.stat()
        except OSError as error:
            raise LakeProbeError(f"cannot snapshot source {path}: {error}") from error
        entries.append((str(path), stat.st_mtime_ns, stat.st_size))
    return tuple(entries)


def is_module_source_path(root: Path, path: Path) -> bool:
    """Whether ``path`` is a visible Lean module source below ``root``.

    Diagnostic probes and logs live below the workspace-level ``.lake`` tree.
    Hidden paths below a source root are nevertheless excluded defensively, so
    a misplaced temporary probe ending in ``.lean`` cannot enter the inventory.
    """

    try:
        relative = path.relative_to(root)
    except ValueError:
        return False
    return path.suffix == ".lean" and all(
        not part.startswith(".") for part in relative.parts
    )


def module_source_files(root: Path) -> tuple[Path, ...]:
    """Return the stable, visible Lean-module inventory below ``root``."""

    return tuple(
        sorted(
            path.resolve()
            for path in root.rglob("*.lean")
            if is_module_source_path(root, path)
        )
    )


def source_tree_matches(
    root: Path,
    paths: Collection[Path],
    snapshot: tuple[tuple[str, int, int], ...],
) -> bool:
    """Check both the module inventory and metadata against a snapshot."""

    expected = tuple(sorted(path.resolve() for path in paths))
    current = module_source_files(root)
    if current != expected:
        return False
    try:
        return source_snapshot(current) == snapshot
    except LakeProbeError:
        return False


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=configured_build_dir())
    parser.add_argument("--lake", type=Path, default=DEFAULT_LAKE)
    parser.add_argument(
        "--probe-timeout",
        type=float,
        default=60.0,
        help="wall timeout for the single no-build Lake planner run",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="test planner parsing and downstream graph classification",
    )
    parser.add_argument("--list-no-green", action="store_true")
    parser.add_argument(
        "--list-frontier",
        action="store_true",
        help="list trace-stale roots whose local imports are all green",
    )
    parser.add_argument("--json", action="store_true")
    return parser.parse_args()


def classify_modules(
    modules: Collection[str],
    local_imports: Mapping[str, Collection[str]],
    stale_roots: Collection[str],
) -> tuple[frozenset[str], frozenset[str], tuple[str, ...]]:
    """Expand Lake's minimal trace-stale roots through reverse imports."""

    module_set = frozenset(modules)
    dependencies = {
        module: frozenset(local_imports.get(module, ())) & module_set
        for module in module_set
    }
    root_set = frozenset(stale_roots)
    unknown = root_set - module_set
    if unknown:
        raise ValueError(f"Lake reported unknown local modules: {sorted(unknown)!r}")

    reverse: dict[str, set[str]] = defaultdict(set)
    for module, imports in dependencies.items():
        for imported in imports:
            reverse[imported].add(module)
    no_green = set(root_set)
    pending = list(root_set)
    while pending:
        dependency = pending.pop()
        for consumer in reverse[dependency]:
            if consumer not in no_green:
                no_green.add(consumer)
                pending.append(consumer)

    frozen_no_green = frozenset(no_green)
    green = module_set - frozen_no_green
    frontier = tuple(
        sorted(
            module
            for module in frozen_no_green
            if dependencies[module] <= green
        )
    )
    return green, frozen_no_green, frontier


def parse_out_of_date_modules(
    output: str, known_modules: Collection[str]
) -> tuple[frozenset[str], tuple[str, ...]]:
    """Extract only Lake's explicit no-build out-of-date diagnostics."""

    known = frozenset(known_modules)
    stale: set[str] = set()
    unexpected_errors: list[str] = []
    building: str | None = None
    for raw_line in output.splitlines():
        line = ANSI_RE.sub("", raw_line).strip()
        match = BUILDING_RE.search(line)
        if match:
            building = match.group("module")
            continue
        if line == OUT_OF_DATE_ERROR:
            if building in known:
                stale.add(building)
            else:
                unexpected_errors.append(
                    f"out-of-date diagnostic without a known module: {building!r}"
                )
            building = None
        elif line.startswith("error:"):
            unexpected_errors.append(line)
    return frozenset(stale), tuple(unexpected_errors)


def lake_trace_stale_roots(
    modules: Collection[str],
    *,
    lake: Path = DEFAULT_LAKE,
    timeout: float = 60.0,
) -> tuple[frozenset[str], float]:
    """Ask Lake once for all minimal trace-stale local module roots.

    ``--no-build`` makes any attempted build action fail before it can execute.
    Deliberately omit ``--old``: old mode falls back to source mtimes after a
    trace-hash mismatch and therefore cannot certify trace freshness.
    """

    if timeout <= 0:
        raise ValueError("probe timeout must be positive")
    if not lake.is_file():
        raise LakeProbeError(f"lake executable is missing: {lake}")
    ordered = tuple(sorted(modules))
    command = lake_no_build_command(lake, ordered)
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise LakeProbeError(f"Lake no-build probe failed: {error}") from error
    elapsed = time.monotonic() - started
    stale, unexpected_errors = parse_out_of_date_modules(
        completed.stdout, ordered
    )
    if unexpected_errors:
        details = "\n".join(unexpected_errors[:10])
        raise LakeProbeError(f"Lake no-build probe reported other errors:\n{details}")
    if completed.returncode == 0:
        if stale:
            raise LakeProbeError(
                "Lake no-build probe returned success with stale diagnostics"
            )
        return stale, elapsed
    if not stale:
        tail = "\n".join(completed.stdout.splitlines()[-20:])
        raise LakeProbeError(
            "Lake no-build probe failed without a recognized trace-stale "
            f"module:\n{tail}"
        )
    return stale, elapsed


def lake_no_build_command(lake: Path, modules: Collection[str]) -> list[str]:
    """Construct the single authoritative, build-action-free probe."""

    return [
        str(lake),
        "--no-build",
        "build",
        *(f"+{module}:olean" for module in sorted(modules)),
    ]


def trace_status(
    modules: Collection[str],
    local_imports: Mapping[str, Collection[str]],
    *,
    lake: Path = DEFAULT_LAKE,
    timeout: float = 60.0,
) -> TraceStatus:
    stale_roots, elapsed = lake_trace_stale_roots(
        modules, lake=lake, timeout=timeout
    )
    green, no_green, frontier = classify_modules(
        modules, local_imports, stale_roots
    )
    return TraceStatus(
        green=green,
        no_green=no_green,
        frontier=frontier,
        stale_roots=tuple(sorted(stale_roots)),
        probe_wall_seconds=elapsed,
    )


def run_self_tests() -> None:
    source_root = Path("/source")
    assert is_module_source_path(source_root, source_root / "A.lean")
    assert is_module_source_path(source_root, source_root / "Sub" / "B.lean")
    assert not is_module_source_path(
        source_root, source_root / ".lake" / "script-progress" / "Probe.lean"
    )
    assert not is_module_source_path(
        source_root, source_root / "Sub" / ".Probe.lean"
    )
    assert not is_module_source_path(
        source_root, Path("/elsewhere/Probe.lean")
    )

    lake = Path("/lake")
    command = lake_no_build_command(lake, {"B", "A"})
    assert command == [
        str(lake),
        "--no-build",
        "build",
        "+A:olean",
        "+B:olean",
    ]
    assert "--old" not in command
    sample = """\
✖ [4/8] Building B
error: target is out-of-date and needs to be rebuilt
✖ [7/8] Building D
error: target is out-of-date and needs to be rebuilt
Some required targets logged failures:
- B
- D
"""
    stale, unexpected = parse_out_of_date_modules(
        sample, {"A", "B", "C", "D"}
    )
    assert stale == {"B", "D"}
    assert not unexpected
    _, unexpected = parse_out_of_date_modules(
        "error: unknown module 'Nope'", {"A"}
    )
    assert unexpected == ("error: unknown module 'Nope'",)

    modules = {"A", "B", "C", "D"}
    imports = {
        "A": set(),
        "B": {"A"},
        "C": {"B"},
        "D": {"A"},
    }
    green, no_green, frontier = classify_modules(modules, imports, {"B", "D"})
    assert green == {"A"}
    assert no_green == {"B", "C", "D"}
    assert frontier == ("B", "D")

    # Artifact timestamp equality is intentionally absent from the contract:
    # if Lake reports no stale trace root, the whole chain is green.
    green, no_green, frontier = classify_modules(modules, imports, set())
    assert green == modules
    assert not no_green
    assert not frontier

    # A missing artifact is surfaced by Lake as a stale root and propagates.
    green, no_green, frontier = classify_modules(modules, imports, {"A"})
    assert not green
    assert no_green == modules
    assert frontier == ("A",)

    # Defensive cycle handling terminates; neither member is an executable
    # frontier while one remains a dependency of the other.
    green, no_green, frontier = classify_modules(
        {"A", "B"}, {"A": {"B"}, "B": {"A"}}, {"A"}
    )
    assert not green
    assert no_green == {"A", "B"}
    assert not frontier


def main() -> int:
    args = parse_args()
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(f"green-status self-test: FAILED: {error}", file=sys.stderr)
            return 1
        print("green-status self-test: OK")
        return 0
    if args.probe_timeout <= 0:
        raise SystemExit("--probe-timeout must be positive")
    build_dir = args.build_dir.resolve()
    configured = configured_build_dir()
    if build_dir != configured:
        raise SystemExit(
            "--build-dir must match lakefile.toml for authoritative trace "
            f"probing: expected {configured}, got {build_dir}"
        )
    files = list(module_source_files(SOURCE_ROOT))
    source_state = source_snapshot(files)
    module_by_file = {
        path: path.relative_to(SOURCE_ROOT).with_suffix("").as_posix().replace("/", ".")
        for path in files
    }
    file_by_module = {module: path for path, module in module_by_file.items()}
    local_imports: dict[str, set[str]] = {}
    for source, module in module_by_file.items():
        text = source.read_text(encoding="utf-8", errors="replace")
        local_imports[module] = {
            name for name in import_modules(text) if name in file_by_module
        }
    modules = sorted(file_by_module)
    try:
        status = trace_status(
            modules,
            local_imports,
            lake=args.lake.resolve(),
            timeout=args.probe_timeout,
        )
    except (LakeProbeError, ValueError) as error:
        print(f"green-status: FAILED: {error}", file=sys.stderr)
        return 2
    if not source_tree_matches(SOURCE_ROOT, files, source_state):
        print(
            "green-status: FAILED: Lean sources changed during the Lake trace "
            "probe; retry for a coherent snapshot",
            file=sys.stderr,
        )
        return 2
    result = {
        "green": len(status.green),
        "total": len(modules),
        "no_green": len(status.no_green),
        "frontier": len(status.frontier),
        "trace_stale_roots": list(status.stale_roots),
        "probe_wall_seconds": round(status.probe_wall_seconds, 3),
        "build_dir": str(build_dir),
        "freshness": "lake_trace_no_build",
    }
    if args.json:
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    else:
        print(
            f"green={result['green']}/{result['total']} "
            f"no_green={result['no_green']} frontier={result['frontier']} "
            f"trace_stale_roots={len(status.stale_roots)} "
            f"probe={status.probe_wall_seconds:.2f}s build_dir={build_dir}"
        )
    if args.list_no_green:
        for module in sorted(status.no_green):
            print(module)
    if args.list_frontier:
        for module in sorted(
            status.frontier,
            key=lambda name: (
                len(file_by_module[name].read_text(
                    encoding="utf-8", errors="replace"
                ).splitlines()),
                name,
            ),
        ):
            line_count = len(file_by_module[module].read_text(
                encoding="utf-8", errors="replace"
            ).splitlines())
            print(f"{line_count:5d}\t{module}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
