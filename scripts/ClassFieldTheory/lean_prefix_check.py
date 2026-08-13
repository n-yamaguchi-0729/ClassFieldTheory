#!/usr/bin/env python3
"""Type-check a prefix of a Lean source file without creating a temporary file."""

from __future__ import annotations

import argparse
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Pipe a source prefix, optional Lean fragments, and namespace closers "
            "to `lake env lean --stdin`."
        )
    )
    parser.add_argument("source", type=Path, help="Lean source path, relative to the Lake root or absolute")
    parser.add_argument(
        "--lines",
        type=int,
        required=True,
        help="last one-based source line to retain",
    )
    parser.add_argument(
        "--start-line",
        type=int,
        default=1,
        help="first one-based source line to retain (default: 1)",
    )
    parser.add_argument(
        "--close",
        action="append",
        default=[],
        metavar="NAMESPACE",
        help="append `end NAMESPACE` (repeat in innermost-to-outermost order)",
    )
    parser.add_argument(
        "--prepend-file",
        action="append",
        default=[],
        type=Path,
        metavar="PATH",
        help=(
            "prepend a UTF-8 Lean fragment before the retained source range "
            "(repeatable; relative paths use the Lake root)"
        ),
    )
    parser.add_argument(
        "--append-file",
        action="append",
        default=[],
        type=Path,
        metavar="PATH",
        help=(
            "append a UTF-8 Lean fragment after the retained prefix "
            "(repeatable; relative paths use the Lake root)"
        ),
    )
    parser.add_argument("--timeout", type=float, default=120.0, help="wall timeout in seconds")
    parser.add_argument(
        "--max-heartbeats",
        type=int,
        help="pass -DmaxHeartbeats=<value> to Lean for this diagnostic run",
    )
    parser.add_argument(
        "--max-rec-depth",
        type=int,
        help="pass -DmaxRecDepth=<value> to Lean for this diagnostic run",
    )
    parser.add_argument("--log", type=Path, help="also write combined Lean output to this path")
    parser.add_argument(
        "--emit-source",
        type=Path,
        help="write the assembled prefix to this .lean file and check that file instead of stdin",
    )
    parser.add_argument(
        "--olean",
        type=Path,
        help="when --emit-source is used, also write the compiled .olean to this path",
    )
    parser.add_argument(
        "--lake",
        type=Path,
        default=Path(shutil.which("lake") or "lake"),
        help="Lake executable",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.start_line <= 0:
        raise SystemExit("--start-line must be positive")
    if args.lines < args.start_line:
        raise SystemExit("--lines must be at least --start-line")
    if args.timeout <= 0:
        raise SystemExit("--timeout must be positive")
    if args.max_heartbeats is not None and args.max_heartbeats <= 0:
        raise SystemExit("--max-heartbeats must be positive")
    if args.max_rec_depth is not None and args.max_rec_depth <= 0:
        raise SystemExit("--max-rec-depth must be positive")
    if args.olean is not None and args.emit_source is None:
        raise SystemExit("--olean requires --emit-source")

    lake_root = Path(__file__).resolve().parents[2]
    source = args.source if args.source.is_absolute() else lake_root / args.source
    source = source.resolve()
    source_lines = source.read_text(encoding="utf-8").splitlines(keepends=True)
    if args.lines > len(source_lines):
        raise SystemExit(f"--lines {args.lines} exceeds source length {len(source_lines)}")

    lean_input = ""
    for fragment_path in args.prepend_file:
        fragment = fragment_path if fragment_path.is_absolute() else lake_root / fragment_path
        fragment_text = fragment.resolve().read_text(encoding="utf-8")
        lean_input += fragment_text
        if fragment_text and not fragment_text.endswith("\n"):
            lean_input += "\n"
    lean_input += "".join(source_lines[args.start_line - 1 : args.lines])
    if lean_input and not lean_input.endswith("\n"):
        lean_input += "\n"
    for fragment_path in args.append_file:
        fragment = fragment_path if fragment_path.is_absolute() else lake_root / fragment_path
        fragment_text = fragment.resolve().read_text(encoding="utf-8")
        lean_input += fragment_text
        if fragment_text and not fragment_text.endswith("\n"):
            lean_input += "\n"
    lean_input += "".join(f"end {namespace}\n" for namespace in args.close)

    started = time.monotonic()
    lean_args: list[str] = []
    if args.max_heartbeats is not None:
        lean_args.append(f"-DmaxHeartbeats={args.max_heartbeats}")
    if args.max_rec_depth is not None:
        lean_args.append(f"-DmaxRecDepth={args.max_rec_depth}")
    lean_command = [str(args.lake), "env", "lean", *lean_args]
    lean_stdin: str | None = lean_input
    if args.emit_source is not None:
        emitted = args.emit_source.resolve()
        emitted.parent.mkdir(parents=True, exist_ok=True)
        emitted.write_text(lean_input, encoding="utf-8")
        lean_command.append(str(emitted))
        lean_stdin = None
        if args.olean is not None:
            olean = args.olean.resolve()
            olean.parent.mkdir(parents=True, exist_ok=True)
            lean_command.extend(["-o", str(olean)])
    else:
        lean_command.append("--stdin")
    process = subprocess.Popen(
        lean_command,
        cwd=lake_root,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    )
    try:
        output, _ = process.communicate(lean_stdin, timeout=args.timeout)
        return_code = process.returncode
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            output, _ = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            output, _ = process.communicate()
        return_code = 124

    elapsed = time.monotonic() - started
    sys.stdout.write(output)
    sys.stdout.write(
        f"prefix-check: source={source} range={args.start_line}-{args.lines} "
        f"prepend_files={len(args.prepend_file)} "
        f"append_files={len(args.append_file)} "
        f"wall={elapsed:.2f}s exit={return_code}\n"
    )
    if args.log:
        log = args.log if args.log.is_absolute() else lake_root / args.log
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(
            output
            + f"prefix-check: source={source} range={args.start_line}-{args.lines} "
            + f"prepend_files={len(args.prepend_file)} "
            + f"append_files={len(args.append_file)} "
            + f"wall={elapsed:.2f}s exit={return_code}\n",
            encoding="utf-8",
        )
    return return_code


if __name__ == "__main__":
    raise SystemExit(main())
