#!/usr/bin/env python3
"""Shared helpers for local Lean development scripts.

The helpers intentionally stay mostly static.  They provide repository discovery,
Lake execution, import parsing, diagnostics parsing, and small source rewriting
utilities used by the standalone scripts in this directory.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, Iterator, Sequence, TypeVar


RE_IMPORT_LINE = re.compile(r"^\s*import\s+(.+?)\s*$")
RE_DIAG = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<col>\d+): (?P<level>error|warning|information): (?P<msg>.*)$"
)
STALE_RE = re.compile(
    r"(\.olean|\.ilean|\.hash|object file|does not exist|invalid import|"
    r"has been modified|out of date|stale)",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class CommandResult:
    command: tuple[str, ...]
    exit_code: int
    output: str
    timed_out: bool = False

    @property
    def ok(self) -> bool:
        return self.exit_code == 0 and not self.timed_out


@dataclass(frozen=True)
class Diagnostic:
    file: str
    line: int
    col: int
    level: str
    message: str
    detail: tuple[str, ...] = ()


@dataclass(frozen=True)
class ImportCommand:
    index: int
    line_no: int
    modules: tuple[str, ...]


@dataclass(frozen=True)
class ImportCandidate:
    path: Path
    line_index: int
    line_no: int
    module: str


_ROOT_CACHE: Path | None = None
T = TypeVar("T")
U = TypeVar("U")


def _looks_like_lean_repo(path: Path) -> bool:
    return (
        (path / "lakefile.lean").is_file()
        or (path / "lakefile.toml").is_file()
        or (path / "lean-toolchain").is_file()
        or (path / "Lean4").is_dir()
    )


def repo_root() -> Path:
    """Return the Lean repository root.

    Installed tools normally live in `<repo>/scripts`, but zip extraction or
    editor integrations may execute them from elsewhere.  The environment
    variable `LEAN_TOOL_ROOT` can override discovery; otherwise we walk upward
    from this file and from the current working directory looking for Lake/Lean
    repository markers.
    """

    global _ROOT_CACHE
    if _ROOT_CACHE is not None:
        return _ROOT_CACHE

    override = os.environ.get("LEAN_TOOL_ROOT")
    if override:
        root = Path(override).expanduser().resolve()
        _ROOT_CACHE = root
        return root

    starts = [Path(__file__).resolve().parent, Path.cwd().resolve()]
    for start in starts:
        for candidate in (start, *start.parents):
            if _looks_like_lean_repo(candidate):
                _ROOT_CACHE = candidate
                return candidate

    _ROOT_CACHE = Path(__file__).resolve().parents[1]
    return _ROOT_CACHE


def lean_root(root: Path | None = None) -> Path:
    return (root or repo_root()) / "Lean4"


def rel(path: Path, root: Path | None = None) -> str:
    root = root or repo_root()
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def dedupe_paths(paths: Iterable[Path]) -> list[Path]:
    seen: set[Path] = set()
    out: list[Path] = []
    for path in paths:
        resolved = path.resolve()
        if resolved not in seen:
            out.append(resolved)
            seen.add(resolved)
    return out


def lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.is_dir():
        env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"
    return env


def run_command(
    command: Sequence[str],
    *,
    timeout: int | None = None,
    cwd: Path | None = None,
    input_text: str | None = None,
) -> CommandResult:
    root = cwd or repo_root()
    try:
        proc = subprocess.run(
            list(command),
            cwd=root,
            env=lake_env(),
            text=True,
            input=input_text,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return CommandResult(tuple(command), proc.returncode, proc.stdout)
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
        output = stdout + stderr
        return CommandResult(tuple(command), 124, output, timed_out=True)


def lake_build(
    targets: Sequence[str],
    *,
    timeout: int = 180,
    rehash: bool = True,
    quiet: bool = True,
    no_ansi: bool = True,
    root: Path | None = None,
) -> CommandResult:
    deduped = [target for target in dict.fromkeys(targets) if target]
    command = ["lake"]
    if rehash:
        command.append("--rehash")
    if quiet:
        command.append("--quiet")
    if no_ansi:
        command.append("--no-ansi")
    command.extend(["build", *deduped])
    return run_command(command, timeout=timeout, cwd=root)


def chunks(xs: Sequence[str], size: int) -> Iterator[list[str]]:
    size = max(1, size)
    for i in range(0, len(xs), size):
        yield list(xs[i : i + size])


def map_with_jobs(items: Sequence[T], fn: Callable[[T], U], *, jobs: int = 1) -> list[U]:
    """Apply `fn` to `items`, preserving input order.

    Most repository scripts are I/O-heavy static scans.  A small thread pool is
    enough to hide filesystem latency without changing result ordering.
    """

    if jobs <= 1 or len(items) <= 1:
        return [fn(item) for item in items]
    results: list[U | None] = [None] * len(items)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        future_to_index = {pool.submit(fn, item): index for index, item in enumerate(items)}
        for future in as_completed(future_to_index):
            results[future_to_index[future]] = future.result()
    return [item for item in results if item is not None]


def atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def write_json_file(path: Path, data: object) -> None:
    atomic_write_text(path, json_dump(data) + "\n")


class ProgressJson:
    def __init__(self, path: Path | None, *, root: Path | None = None) -> None:
        self.path = path
        self.root = root or repo_root()

    def write(self, data: dict[str, object]) -> None:
        if self.path is None:
            return
        path = self.path if self.path.is_absolute() else self.root / self.path
        payload = dict(data)
        payload["updated_at"] = datetime.now(timezone.utc).isoformat()
        payload["pid"] = os.getpid()
        payload["progress_json"] = rel(path, self.root)
        write_json_file(path, payload)


def strip_comments_preserve_lines(text: str, *, strip_strings: bool = False) -> str:
    """Replace comments and optionally strings by spaces while preserving lines.

    Handles nested Lean block comments.  It is not a full Lean parser, but it is
    reliable enough for static scans and avoids the most damaging false matches
    in comments and string literals.
    """

    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        ch = text[i]
        nxt2 = text[i : i + 2]

        if depth == 0 and not in_string and nxt2 == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if not in_string and nxt2 == "/-":
            depth += 1
            out.extend("  ")
            i += 2
            continue

        if depth and nxt2 == "-/":
            depth -= 1
            out.extend("  ")
            i += 2
            continue

        if depth:
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if strip_strings:
            if not in_string and ch == '"':
                in_string = True
                escaped = False
                out.append(" ")
                i += 1
                continue
            if in_string:
                out.append("\n" if ch == "\n" else " ")
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
                i += 1
                continue

        out.append(ch)
        i += 1

    return "".join(out)


def import_commands(text: str) -> list[ImportCommand]:
    clean = strip_comments_preserve_lines(text)
    out: list[ImportCommand] = []
    for index, line in enumerate(clean.splitlines()):
        match = RE_IMPORT_LINE.match(line)
        if match:
            modules = tuple(part for part in match.group(1).split() if part)
            if modules:
                out.append(ImportCommand(index=index, line_no=index + 1, modules=modules))
    return out


def import_modules(text: str) -> list[str]:
    modules: list[str] = []
    for command in import_commands(text):
        modules.extend(command.modules)
    return modules


def import_candidates(path: Path, text: str | None = None, only: set[str] | None = None) -> list[ImportCandidate]:
    text = path.read_text(encoding="utf-8", errors="replace") if text is None else text
    only = only or set()
    out: list[ImportCandidate] = []
    for command in import_commands(text):
        for module in command.modules:
            if only and module not in only:
                continue
            out.append(ImportCandidate(path=path, line_index=command.index, line_no=command.line_no, module=module))
    return out


def is_import_only(text: str) -> bool:
    for line in strip_comments_preserve_lines(text).splitlines():
        if not line.strip():
            continue
        if RE_IMPORT_LINE.match(line):
            continue
        return False
    return True


def initial_import_block_bounds(text: str) -> tuple[int, int] | None:
    """Return line bounds [start, end) for the leading import block.

    Blank lines, line comments, and block comments before imports are considered
    part of the preamble and are preserved.  Only consecutive leading import
    commands are rewritten by import-normalization tools.  After the first
    import, only actual blank lines are included in the block; comments such as
    module docs belong to the file body and must not be rewritten away.
    """

    lines = text.splitlines()
    clean_lines = strip_comments_preserve_lines(text).splitlines()
    start: int | None = None
    end: int | None = None
    for idx, clean in enumerate(clean_lines):
        stripped = clean.strip()
        if RE_IMPORT_LINE.match(clean):
            if start is None:
                start = idx
            end = idx + 1
            continue
        if start is None:
            if stripped == "":
                continue
            return None
        if lines[idx].strip() == "":
            # Allow blank lines within the import preamble; they will be
            # normalized away only if the block is actually rewritten.
            end = idx + 1
            continue
        break
    if start is None or end is None:
        return None
    return start, end


def unique_import_modules(modules: Iterable[str], *, sort_modules: bool = False) -> list[str]:
    deduped = list(dict.fromkeys(modules))
    return sorted(deduped) if sort_modules else deduped


def rewrite_initial_import_block(text: str, modules: Sequence[str]) -> str:
    lines = text.splitlines(keepends=True)
    bounds = initial_import_block_bounds(text)
    newline = "\n"
    if bounds is None:
        replacement = [f"import {module}{newline}" for module in modules]
        return "".join([*replacement, *([] if not modules else [newline]), *lines])
    start, end = bounds
    replacement = [f"import {module}{newline}" for module in modules]
    if replacement and end < len(lines) and lines[end].strip():
        replacement.append(newline)
    lines[start:end] = replacement
    return "".join(lines)


def remove_import_modules(text: str, modules_to_remove: Iterable[str]) -> tuple[str, list[str]]:
    """Remove all occurrences of selected modules from Lean import commands."""

    remove = set(modules_to_remove)
    if not remove:
        return text, []
    lines = text.splitlines(keepends=True)
    commands = {command.index: command for command in import_commands(text)}
    removed: list[str] = []
    for index in sorted(commands, reverse=True):
        command = commands[index]
        kept = [module for module in command.modules if module not in remove]
        gone = [module for module in command.modules if module in remove]
        if not gone:
            continue
        removed.extend(gone)
        if kept:
            newline = "\n" if lines[index].endswith("\n") else ""
            lines[index] = f"import {' '.join(kept)}{newline}"
        else:
            del lines[index]
    removed.reverse()
    return "".join(lines), removed


def add_import(text: str, module: str) -> tuple[str, bool]:
    if module in import_modules(text):
        return text, False
    lines = text.splitlines(keepends=True)
    commands = import_commands(text)
    insert_at = commands[-1].index + 1 if commands else 0
    lines.insert(insert_at, f"import {module}\n")
    return "".join(lines), True


def module_for_file(path: Path, *, root: Path | None = None) -> str | None:
    root = root or repo_root()
    lroot = lean_root(root)
    path = path.resolve()
    if path.parent == root.resolve() and path.suffix == ".lean":
        return path.stem
    try:
        rel_path = path.relative_to(lroot.resolve())
    except ValueError:
        return None
    return rel_path.with_suffix("").as_posix().replace("/", ".")


def file_for_module(module: str, *, root: Path | None = None) -> Path | None:
    root = root or repo_root()
    root_candidate = root / f"{module}.lean"
    if root_candidate.is_file():
        return root_candidate.resolve()
    lean_candidate = lean_root(root) / f"{module.replace('.', '/')}.lean"
    if lean_candidate.is_file():
        return lean_candidate.resolve()
    return None


def default_library_files(*, root: Path | None = None) -> list[Path]:
    root = root or repo_root()
    files: list[Path] = []
    root_entry = root / "Lean4.lean"
    if root_entry.is_file():
        files.append(root_entry.resolve())
    lroot = lean_root(root)
    if lroot.is_dir():
        files.extend(path.resolve() for path in sorted(lroot.rglob("*.lean")))
    return dedupe_paths(files)


def all_repo_lean_files(*, root: Path | None = None) -> list[Path]:
    root = root or repo_root()
    ignored = {".git", ".lake", "__pycache__"}
    files: list[Path] = []
    for path in root.rglob("*.lean"):
        if any(part in ignored for part in path.relative_to(root).parts):
            continue
        files.append(path.resolve())
    return dedupe_paths(sorted(files))


def resolve_target_files(raw: str, *, root: Path | None = None) -> list[Path]:
    root = root or repo_root()
    raw = raw.removeprefix("./")
    path = Path(raw)
    if not path.is_absolute():
        path = root / path

    if path.is_file():
        if path.suffix != ".lean":
            raise SystemExit(f"not a Lean file: {raw}")
        return [path.resolve()]
    if path.is_dir():
        return dedupe_paths(sorted(p.resolve() for p in path.rglob("*.lean")))
    if raw.endswith(".lean"):
        raise SystemExit(f"Lean file not found: {raw}")

    files: list[Path] = []
    module_path = raw.replace(".", "/")
    for candidate in (root / f"{module_path}.lean", lean_root(root) / f"{module_path}.lean"):
        if candidate.is_file():
            files.append(candidate.resolve())
    for candidate in (root / module_path, lean_root(root) / module_path):
        if candidate.is_dir():
            files.extend(path.resolve() for path in sorted(candidate.rglob("*.lean")))
    if not files:
        raise SystemExit(f"unknown target: {raw}")
    return dedupe_paths(files)


def build_target(path: Path, *, facet: str = "olean", root: Path | None = None) -> str:
    module = module_for_file(path, root=root)
    suffix = f":{facet}" if facet else ""
    if module is not None:
        return f"+{module}{suffix}"
    return f"{rel(path, root)}{suffix}"


def parse_diagnostics(output: str) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    current: dict[str, object] | None = None
    details: list[str] = []

    def flush() -> None:
        nonlocal current, details
        if current is None:
            return
        diagnostics.append(
            Diagnostic(
                file=str(current["file"]),
                line=int(current["line"]),
                col=int(current["col"]),
                level=str(current["level"]),
                message=str(current["message"]).strip(),
                detail=tuple(line.rstrip() for line in details if line.strip()),
            )
        )
        current = None
        details = []

    for raw in output.splitlines():
        match = RE_DIAG.match(raw)
        if match:
            flush()
            current = {
                "file": match.group("file"),
                "line": int(match.group("line")),
                "col": int(match.group("col")),
                "level": match.group("level"),
                "message": match.group("msg"),
            }
        elif current is not None:
            details.append(raw)
    flush()
    return diagnostics


def compact_output(output: str, max_lines: int, *, interesting: Sequence[str] = ()) -> str:
    lines = output.splitlines()
    if len(lines) <= max_lines:
        return output.rstrip()
    markers = tuple(interesting) or (
        ": error:",
        ": warning:",
        "linter reports",
        "not used in the remainder of the type",
        "tactic does nothing",
        "REMOVE ",
        "KEEP ",
        "ENV ",
        "ZERO |",
        "DUP",
        "MISSING-DOC",
        "NAME-LINT",
        "DEAD-PRIVATE",
    )
    picked: list[str] = []
    for line in lines:
        if any(marker in line for marker in markers):
            picked.append(line)
            if len(picked) >= max_lines:
                return "\n".join(picked) + f"\n... {len(lines) - max_lines} more lines"
    return "\n".join(lines[:max_lines]) + f"\n... {len(lines) - max_lines} more lines"


def diagnostic_files(output: str, *, root: Path | None = None) -> set[Path]:
    root = root or repo_root()
    files: set[Path] = set()
    for diag in parse_diagnostics(output):
        if diag.level != "error":
            continue
        path = Path(diag.file)
        if not path.is_absolute():
            path = root / path
        try:
            files.add(path.resolve())
        except OSError:
            pass
    return files


def json_dump(data: object) -> str:
    return json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True)


def print_command_result(result: CommandResult, *, max_lines: int = 80) -> None:
    print("+ " + " ".join(result.command))
    if result.timed_out:
        print("TIMEOUT")
    print(f"exit code: {result.exit_code}")
    if result.output.strip():
        print(compact_output(result.output, max_lines))
