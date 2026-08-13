#!/usr/bin/env python3
"""Build one or more ClassFieldTheory targets in one locked Lake process.

All targets share the build directory configured by the workspace lakefile.
The process-wide lock prevents two Lake planners from writing the same olean
dependency concurrently; callers that want parallel elaboration should pass
all independent targets to this runner in a single invocation.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent.parent
LAKEFILE = ROOT / "lakefile.toml"
LOCK = ROOT / ".lake" / "script-progress" / "cft-target-build.lock"
LOG_ROOT = ROOT / ".lake" / "script-progress" / "cft-target-logs"


def configured_build_dir() -> Path:
    with LAKEFILE.open("rb") as stream:
        raw = tomllib.load(stream).get("buildDir")
    if not isinstance(raw, str) or not raw:
        raise RuntimeError("lakefile.toml must define one nonempty buildDir")
    result = (ROOT / raw).resolve()
    lake_root = (ROOT / ".lake").resolve()
    if result != lake_root and lake_root not in result.parents:
        raise RuntimeError(f"configured buildDir is outside .lake: {result}")
    return result


def lake_executable() -> str:
    """Resolve Lake even when Codex starts WSL without a login-shell PATH."""
    discovered = shutil.which("lake")
    if discovered is not None:
        return discovered
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.is_file() and os.access(elan_lake, os.X_OK):
        return str(elan_lake)
    raise RuntimeError("lake is unavailable on PATH and ~/.elan/bin/lake is absent")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build several CFT targets with one locked Lake planner."
    )
    parser.add_argument(
        "targets",
        nargs="+",
        help="Lake targets or module names; pass several to share one plan",
    )
    parser.add_argument(
        "--wait",
        action="store_true",
        help="wait for an existing managed CFT build instead of failing",
    )
    return parser.parse_args()


def active_workspace_build_processes() -> list[str]:
    """Return unmanaged Lake/Lean writers currently using this workspace."""
    active: list[str] = []
    proc_root = Path("/proc")
    for process_dir in proc_root.iterdir():
        if not process_dir.name.isdigit():
            continue
        try:
            command = (process_dir / "comm").read_text(
                encoding="utf-8", errors="replace"
            ).strip()
            if command not in {"lake", "lean"}:
                continue
            arguments = (process_dir / "cmdline").read_bytes().replace(
                b"\0", b" "
            ).decode("utf-8", errors="replace")
            cwd = (process_dir / "cwd").resolve()
        except (FileNotFoundError, PermissionError, OSError):
            continue
        is_workspace_lake = command == "lake" and cwd == ROOT
        is_cft_lean = (
            command == "lean"
            and str(ROOT / "Lean4" / "ClassFieldTheory") in arguments
        )
        if is_workspace_lake or is_cft_lean:
            active.append(f"pid={process_dir.name} {arguments.strip()}")
    return sorted(active)


def main() -> int:
    args = parse_args()
    build_dir = configured_build_dir()
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    log_path = LOG_ROOT / f"targets-{timestamp}-{os.getpid()}.log"

    with LOCK.open("a+", encoding="utf-8") as lock_stream:
        operation = fcntl.LOCK_EX
        if not args.wait:
            operation |= fcntl.LOCK_NB
        try:
            fcntl.flock(lock_stream.fileno(), operation)
        except BlockingIOError:
            print(
                "another managed ClassFieldTheory build owns "
                f"{LOCK}; combine targets or retry after it exits",
                file=sys.stderr,
            )
            return 2
        lock_stream.seek(0)
        lock_stream.truncate()
        lock_stream.write(
            f"pid={os.getpid()} targets={' '.join(args.targets)}\n"
        )
        lock_stream.flush()

        unmanaged = active_workspace_build_processes()
        if unmanaged:
            print(
                "unmanaged ClassFieldTheory Lake/Lean writer is active; "
                "wait for it instead of starting an overlapping planner:",
                file=sys.stderr,
            )
            for process in unmanaged:
                print(f"  {process}", file=sys.stderr)
            return 3

        command = [
            lake_executable(),
            f"-KbuildDir={build_dir.relative_to(ROOT).as_posix()}",
            "build",
            *args.targets,
        ]
        environment = os.environ.copy()
        environment["LEAN_NUM_THREADS"] = "1"
        print(f"buildDir={build_dir}")
        print(f"log={log_path}")
        print("command=" + " ".join(command))
        with log_path.open("w", encoding="utf-8") as log_stream:
            process = subprocess.Popen(
                command,
                cwd=ROOT,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            assert process.stdout is not None
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                log_stream.write(line)
                log_stream.flush()
            return process.wait()


if __name__ == "__main__":
    raise SystemExit(main())
