#!/usr/bin/env python3
"""Build the current non-green frontier serially and never rebuild green targets.

The default mode is a read-only dry run.  ``--execute`` snapshots the current
frontier, removes any repeatable ``--exclude MODULE`` selections, acquires an
exclusive lock, and invokes exactly one
``LEAN_NUM_THREADS=1 lake build +<module>:olean`` process at a time,
shortest source first.  Limiting the Lean runtime thread pool also prevents a
single Lake process from launching sibling dependency builds concurrently.
It stops at the first failure, writes one log per attempted module, and reports
the diagnostic-warning count and fresh-green count after every build.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import uuid


SCRIPT_DIR = Path(__file__).resolve().parent
TOOLS_DIR = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))
sys.path.insert(0, str(TOOLS_DIR))

from _lean_tool_common import import_modules, repo_root  # noqa: E402
from green_status import (  # noqa: E402
    LakeProbeError,
    classify_modules,
    configured_build_dir,
    production_module_name,
    production_source_files,
    production_source_tree_matches,
    source_snapshot,
    trace_status,
)


ROOT = repo_root()
DEFAULT_LOCK = ROOT / ".lake" / "script-progress" / "cft-frontier-build.lock"
DEFAULT_LOG_ROOT = ROOT / ".lake" / "script-progress" / "cft-frontier-logs"
LEAN_SINGLE_JOB_ENV = "LEAN_NUM_THREADS=1"


@dataclass(frozen=True)
class LibraryState:
    files: dict[str, Path]
    imports: dict[str, frozenset[str]]
    green: frozenset[str]
    no_green: frozenset[str]
    frontier: tuple[str, ...]
    stale_roots: tuple[str, ...]
    probe_wall_seconds: float
    line_counts: dict[str, int]


class ExclusiveLock:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.token = f"pid={os.getpid()} token={uuid.uuid4()}\n"
        self.owned = False

    def __enter__(self) -> "ExclusiveLock":
        self.path.parent.mkdir(parents=True, exist_ok=True)
        try:
            descriptor = os.open(
                self.path,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                0o644,
            )
        except FileExistsError as error:
            try:
                owner = self.path.read_text(encoding="utf-8").strip()
            except OSError:
                owner = "unreadable owner"
            raise RuntimeError(
                f"frontier build lock already exists: {self.path} ({owner})"
            ) from error
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(self.token)
        self.owned = True
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        if not self.owned:
            return
        try:
            if self.path.read_text(encoding="utf-8") == self.token:
                self.path.unlink()
        finally:
            self.owned = False


def collect_state(
    build_dir: Path, *, lake: Path, probe_timeout: float
) -> LibraryState:
    sources = list(production_source_files())
    source_state = source_snapshot(sources)
    files = {
        production_module_name(path): path
        for path in sources
    }
    modules = set(files)
    texts = {
        module: path.read_text(encoding="utf-8", errors="replace")
        for module, path in files.items()
    }
    imports = {
        module: frozenset(
            imported
            for imported in import_modules(texts[module])
            if imported in modules
        )
        for module in files
    }
    line_counts = {
        module: len(text.splitlines()) for module, text in texts.items()
    }
    status = trace_status(
        modules,
        imports,
        lake=lake,
        timeout=probe_timeout,
    )
    if not production_source_tree_matches(sources, source_state):
        raise LakeProbeError(
            "Lean sources changed during the Lake trace probe; retry for a "
            "coherent frontier snapshot"
        )
    ordered_frontier = tuple(
        sorted(
            status.frontier,
            key=lambda module: (line_counts[module], module),
        )
    )
    return LibraryState(
        files=files,
        imports=imports,
        green=status.green,
        no_green=status.no_green,
        frontier=ordered_frontier,
        stale_roots=status.stale_roots,
        probe_wall_seconds=status.probe_wall_seconds,
        line_counts=line_counts,
    )


def lake_build_command(lake: Path, module: str) -> list[str]:
    return [
        "/usr/bin/env",
        LEAN_SINGLE_JOB_ENV,
        str(lake),
        "build",
        f"+{module}:olean",
    ]


def safe_log_name(module: str) -> str:
    return module.replace(".", "__") + ".log"


def run_build(
    command: list[str], *, timeout: float | None
) -> tuple[int, str, float]:
    started = time.monotonic()
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    )
    try:
        output, _ = process.communicate(timeout=timeout)
        return_code = process.returncode
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            output, _ = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            output, _ = process.communicate()
        return_code = 124
        output += f"\nfrontier-build: TIMEOUT after {timeout:.2f}s\n"
    return return_code, output, time.monotonic() - started


def count_warning_diagnostics(output: str) -> int:
    """Count Lean/Lake warning diagnostics without turning them into errors."""
    return sum(
        line.lstrip().startswith("warning:")
        for line in output.splitlines()
    )


def select_frontier(
    frontier: tuple[str, ...],
    excluded: frozenset[str],
    max_modules: int,
) -> tuple[str, ...]:
    """Filter one ordered frontier snapshot before applying its size limit."""
    available = tuple(module for module in frontier if module not in excluded)
    return available[: max_modules if max_modules else len(available)]


def dry_run_payload(
    state: LibraryState,
    selected: tuple[str, ...],
    excluded: frozenset[str],
    lake: Path,
) -> dict[str, object]:
    return {
        "green": len(state.green),
        "total": len(state.files),
        "no_green": len(state.no_green),
        "frontier": len(state.frontier),
        "excluded": [
            module for module in state.frontier if module in excluded
        ],
        "trace_stale_roots": list(state.stale_roots),
        "probe_wall_seconds": round(state.probe_wall_seconds, 3),
        "freshness": "lake_trace_no_build",
        "selected": [
            {
                "module": module,
                "lines": state.line_counts[module],
                "command": lake_build_command(lake, module),
            }
            for module in selected
        ],
    }


def run_self_tests() -> None:
    modules = {"A", "B", "C", "D"}
    imports = {
        "A": frozenset(),
        "B": frozenset({"A"}),
        "C": frozenset({"B"}),
        "D": frozenset({"A"}),
    }
    green, no_green, frontier = classify_modules(
        modules,
        imports,
        {"B", "D"},
    )
    assert green == {"A"}
    assert no_green == {"B", "C", "D"}
    assert frontier == ("B", "D")
    assert lake_build_command(Path("/lake"), "A.B") == [
        "/usr/bin/env",
        "LEAN_NUM_THREADS=1",
        "/lake",
        "build",
        "+A.B:olean",
    ]
    assert count_warning_diagnostics(
        "warning: first\ninfo: ignored\n  warning: second\n"
    ) == 2
    ordered_frontier = ("Short", "Excluded", "Long")
    assert select_frontier(
        ordered_frontier,
        frozenset({"Excluded"}),
        0,
    ) == ("Short", "Long")
    assert select_frontier(
        ordered_frontier,
        frozenset({"Short"}),
        1,
    ) == ("Excluded",)
    with tempfile.TemporaryDirectory() as directory:
        lock_path = Path(directory) / "runner.lock"
        with ExclusiveLock(lock_path):
            assert lock_path.is_file()
            try:
                with ExclusiveLock(lock_path):
                    raise AssertionError("second lock unexpectedly succeeded")
            except RuntimeError:
                pass
        assert not lock_path.exists()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--execute",
        action="store_true",
        help="run the printed commands; default is a read-only dry run",
    )
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--json", action="store_true", help="JSON dry-run output")
    parser.add_argument("--build-dir", type=Path, default=configured_build_dir())
    parser.add_argument(
        "--lake",
        type=Path,
        default=Path(shutil.which("lake") or "lake"),
    )
    parser.add_argument("--lock-file", type=Path, default=DEFAULT_LOCK)
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument(
        "--max-modules",
        type=int,
        default=0,
        help="limit the current frontier snapshot; zero means all",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="MODULE",
        help=(
            "exclude MODULE from the current frontier snapshot; may be "
            "specified more than once"
        ),
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=0.0,
        help="per-module wall timeout in seconds; zero disables it",
    )
    parser.add_argument(
        "--probe-timeout",
        type=float,
        default=60.0,
        help="wall timeout for each no-build Lake freshness probe",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.max_modules < 0:
        raise SystemExit("--max-modules must be nonnegative")
    if args.timeout < 0:
        raise SystemExit("--timeout must be nonnegative")
    if args.probe_timeout <= 0:
        raise SystemExit("--probe-timeout must be positive")
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(f"frontier-build self-test: FAILED: {error}", file=sys.stderr)
            return 1
        print("frontier-build self-test: OK")
        return 0

    build_dir = args.build_dir.resolve()
    configured = configured_build_dir()
    if build_dir != configured:
        raise SystemExit(
            "--build-dir must match lakefile.toml for authoritative trace "
            f"probing: expected {configured}, got {build_dir}"
        )
    try:
        state = collect_state(
            build_dir,
            lake=args.lake.resolve(),
            probe_timeout=args.probe_timeout,
        )
    except (LakeProbeError, ValueError) as error:
        print(f"frontier-build: freshness probe FAILED: {error}", file=sys.stderr)
        return 2
    excluded = frozenset(args.exclude)
    selected = select_frontier(state.frontier, excluded, args.max_modules)
    payload = dry_run_payload(state, selected, excluded, args.lake)
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        mode = "EXECUTE" if args.execute else "DRY-RUN"
        print(
            f"frontier-build: {mode} green={len(state.green)}/{len(state.files)} "
            f"no_green={len(state.no_green)} frontier={len(state.frontier)} "
            f"excluded={sum(module in excluded for module in state.frontier)} "
            f"selected={len(selected)}"
        )
        for module in selected:
            command = " ".join(lake_build_command(args.lake, module))
            print(
                f"  {state.line_counts[module]:5d} lines  {module}\n"
                f"    {command}"
            )
    if not args.execute:
        return 0
    if args.json:
        raise SystemExit("--json is available only in dry-run mode")
    if not selected:
        print("frontier-build: nothing to build")
        return 0
    if not args.lake.is_file():
        raise SystemExit(f"lake executable is missing: {args.lake}")

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    log_dir = (args.log_dir or (DEFAULT_LOG_ROOT / timestamp)).resolve()
    timeout = args.timeout or None
    with ExclusiveLock(args.lock_file.resolve()):
        log_dir.mkdir(parents=True, exist_ok=False)
        for module in selected:
            try:
                current = collect_state(
                    build_dir,
                    lake=args.lake.resolve(),
                    probe_timeout=args.probe_timeout,
                )
            except (LakeProbeError, ValueError) as error:
                print(
                    f"frontier-build: freshness probe FAILED: {error}",
                    file=sys.stderr,
                )
                return 2
            if module in current.green:
                print(f"frontier-build: skip newly green module {module}")
                continue
            if module not in current.frontier:
                print(
                    f"frontier-build: STOP {module} is no longer in the current frontier",
                    file=sys.stderr,
                )
                return 1
            command = lake_build_command(args.lake, module)
            return_code, output, elapsed = run_build(command, timeout=timeout)
            warning_count = count_warning_diagnostics(output)
            probe_error: str | None = None
            try:
                refreshed = collect_state(
                    build_dir,
                    lake=args.lake.resolve(),
                    probe_timeout=args.probe_timeout,
                )
            except (LakeProbeError, ValueError) as error:
                refreshed = None
                probe_error = str(error)
                summary = (
                    f"frontier-build: module={module} wall={elapsed:.2f}s "
                    f"exit={return_code} warnings={warning_count} "
                    f"freshness_probe_error={probe_error}\n"
                )
            else:
                summary = (
                    f"frontier-build: module={module} wall={elapsed:.2f}s "
                    f"exit={return_code} warnings={warning_count} "
                    f"green={len(refreshed.green)}/"
                    f"{len(refreshed.files)}\n"
                )
            log_path = log_dir / safe_log_name(module)
            log_path.write_text(output + summary, encoding="utf-8")
            sys.stdout.write(output)
            sys.stdout.write(summary)
            print(f"frontier-build: log={log_path}")
            if probe_error is not None:
                print(
                    "frontier-build: post-build freshness probe FAILED: "
                    f"{probe_error}",
                    file=sys.stderr,
                )
                return 2
            if return_code != 0:
                print("frontier-build: STOP after first failure", file=sys.stderr)
                return return_code
            assert refreshed is not None
            if module not in refreshed.green:
                print(
                    "frontier-build: STOP build returned success but target is not green",
                    file=sys.stderr,
                )
                return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
