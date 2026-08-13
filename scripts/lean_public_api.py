#!/usr/bin/env python3
"""Static public-API audit and snapshot tool for Lean libraries.

The tool is deliberately static: it does not elaborate Lean files.  That makes
it cheap enough to run before every commit and in CI.  It answers questions that
matter once a Lean project is becoming a public library:

* which public declarations exist;
* which public declarations have no docstring;
* which names were added, removed, or changed since a previous API snapshot;
* where axioms/opaques/public instances/nolints/TODOs still appear.

Static parsing is conservative.  Use it as a hygiene gate, not as a proof of
semantic API equivalence.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

from _lean_tool_common import (
    default_library_files,
    import_modules,
    json_dump,
    map_with_jobs,
    rel,
    repo_root,
    resolve_target_files,
    strip_comments_preserve_lines,
    write_json_file,
)

ROOT = repo_root()

DECL_RE = re.compile(
    r"^\s*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|constant)\b"
    r"(?:\s+(?P<name>[^\s:{(\[]+))?"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(.+?)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+(.+?))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(.+?))?\s*$")
ATTR_RE = re.compile(r"@\[([^\]]+)\]")
TODO_RE = re.compile(r"\b(TODO|FIXME|HACK|XXX|temporary|workaround)\b", re.IGNORECASE)
HARD_RE = re.compile(r"\b(axiom|opaque|admit)\b|set_option\s+warn\.sorry\s+false")
NOLINT_RE = re.compile(r"\bnolint\b|set_option\s+linter\.[A-Za-z0-9_.]+\s+false")
PUBLIC_DOC_KINDS = {"theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "axiom", "opaque", "constant"}
DEFAULT_REQUIRE_DOCS = ("theorem", "lemma", "def", "structure", "class")


@dataclass(frozen=True)
class Declaration:
    name: str
    short_name: str
    kind: str
    file: str
    line: int
    documented: bool
    doc_line: int | None
    private: bool
    protected: bool
    unsafe: bool
    noncomputable: bool
    attributes: tuple[str, ...]
    modifiers: tuple[str, ...]


@dataclass(frozen=True)
class FileAudit:
    file: str
    loc: int
    imports: int
    declarations: int
    public_declarations: int
    documented_public: int
    missing_doc_public: int
    sorry_tokens: int
    hard_placeholders: int
    nolint_suppressions: int
    todos: int
    longest_line: int


@dataclass
class Scope:
    kind: str
    names: tuple[str, ...] = ()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def hard_placeholder_count(path: Path, clean: str, allow_patterns: tuple[re.Pattern[str], ...]) -> int:
    count = 0
    clean_lines = clean.splitlines()
    for match in HARD_RE.finditer(clean):
        line_no = clean.count("\n", 0, match.start()) + 1
        line_text = clean_lines[line_no - 1] if line_no - 1 < len(clean_lines) else match.group(0)
        if allow_patterns:
            haystack = "\n".join([f"{rel(path, ROOT)}:{line_no}", line_text, match.group(0)])
            if any(pattern.search(haystack) for pattern in allow_patterns):
                continue
        count += 1
    return count


def clean_name(raw: str | None, kind: str, fallback_index: int) -> str:
    if raw is None or raw.startswith(":") or raw.startswith("(") or raw.startswith("["):
        if kind == "instance":
            return f"_anonymous_instance_{fallback_index}"
        return f"_anonymous_{kind}_{fallback_index}"
    return raw.strip().rstrip(",")


def find_decl_name(
    raw: str | None,
    kind: str,
    fallback_index: int,
    clean_lines: list[str],
    current_idx: int,
) -> tuple[str, int | None]:
    """Return the syntactic declaration name and its line when it is split onto the next line.

    Lean permits a style such as

    ```
    theorem
        veryLongName ...
    ```

    The public-library scanner is static, so it only needs a conservative recovery of the next
    identifier token.  Anonymous instances deliberately remain anonymous; otherwise their target
    type on the next line would be mistaken for an instance name.
    """
    direct = clean_name(raw, kind, fallback_index)
    if not direct.startswith("_anonymous_") or kind == "instance":
        return direct, None
    for lookahead in range(current_idx, min(len(clean_lines), current_idx + 5)):
        stripped = clean_lines[lookahead].strip()
        if not stripped:
            continue
        token = stripped.split(maxsplit=1)[0].rstrip(",")
        if not token or token in {"where", ":=", "|"}:
            continue
        if token[0] in ":({[":
            continue
        return clean_name(token, kind, fallback_index), lookahead + 1
    return direct, None


def namespace_prefix(scopes: list[Scope]) -> list[str]:
    out: list[str] = []
    for scope in scopes:
        if scope.kind == "namespace":
            out.extend(scope.names)
    return out


def qualify_name(short: str, scopes: list[Scope]) -> str:
    if short.startswith("_root_."):
        return short.removeprefix("_root_.")
    ns = namespace_prefix(scopes)
    if not ns:
        return short
    prefix = ".".join(ns)
    # In Lean, dotted declaration names are still relative to the current
    # namespace unless `_root_.` is used.  Avoid duplicating an already explicit
    # current prefix, but otherwise qualify dotted names as well.
    if short == prefix or short.startswith(prefix + "."):
        return short
    return ".".join([*ns, short])


def parse_docstring_start(line: str) -> bool:
    stripped = line.lstrip()
    return stripped.startswith("/--") and not stripped.startswith("/---")


def parse_attrs(line: str) -> tuple[str, ...]:
    attrs: list[str] = []
    for match in ATTR_RE.finditer(line):
        attrs.extend(part.strip() for part in match.group(1).split(",") if part.strip())
    return tuple(attrs)


def pop_scope(scopes: list[Scope], name: str | None) -> None:
    if not scopes:
        return
    if not name:
        scopes.pop()
        return
    targets = [part for part in name.split() if part]
    if not targets:
        scopes.pop()
        return
    for target in reversed(targets):
        for idx in range(len(scopes) - 1, -1, -1):
            scope = scopes[idx]
            if target in scope.names or (len(scope.names) == 1 and scope.names[0] == target):
                del scopes[idx:]
                break
        else:
            if scopes:
                scopes.pop()


def scan_declarations(path: Path, *, include_private: bool = False, text: str | None = None) -> list[Declaration]:
    text = read_text(path) if text is None else text
    lines = text.splitlines()
    clean_lines = strip_comments_preserve_lines(text).splitlines()
    scopes: list[Scope] = []
    declarations: list[Declaration] = []
    pending_doc: tuple[int, str] | None = None
    pending_attrs: list[str] = []
    in_doc = False
    doc_start_line: int | None = None
    doc_buffer: list[str] = []

    for idx, original in enumerate(lines, 1):
        clean = clean_lines[idx - 1] if idx - 1 < len(clean_lines) else original
        stripped_original = original.strip()
        stripped_clean = clean.strip()

        if in_doc:
            doc_buffer.append(original)
            if "-/" in original:
                pending_doc = (doc_start_line or idx, "\n".join(doc_buffer))
                in_doc = False
                doc_start_line = None
                doc_buffer = []
            continue

        if parse_docstring_start(original):
            doc_start_line = idx
            doc_buffer = [original]
            if "-/" in original:
                pending_doc = (idx, original)
                doc_start_line = None
                doc_buffer = []
            else:
                in_doc = True
            continue

        attr_tuple = parse_attrs(original)
        if attr_tuple:
            pending_attrs.extend(attr_tuple)
            # Attributes can appear either on their own line or inline before a
            # declaration, e.g. `@[simp] theorem foo ...`.  The old scanner
            # treated every attribute line as standalone and therefore missed
            # inline attributed declarations, sometimes leaking the attribute to
            # the next declaration.
            clean_without_attrs = ATTR_RE.sub("", clean).strip()
            if not clean_without_attrs:
                continue
            clean = ATTR_RE.sub("", clean)
            stripped_clean = clean.strip()

        ns = NAMESPACE_RE.match(clean)
        if ns:
            parts = tuple(part for part in ns.group(1).split() if part)
            if parts:
                scopes.append(Scope("namespace", parts))
            pending_doc = None
            pending_attrs.clear()
            continue

        sec = SECTION_RE.match(clean)
        if sec:
            names = tuple(part for part in (sec.group(1) or "").split() if part)
            scopes.append(Scope("section", names))
            pending_doc = None
            pending_attrs.clear()
            continue

        end = END_RE.match(clean)
        if end:
            pop_scope(scopes, end.group(1))
            pending_doc = None
            pending_attrs.clear()
            continue

        match = DECL_RE.match(clean)
        if match:
            kind = match.group("kind")
            modifiers = tuple(part for part in match.group("mods").split() if part)
            short_name, name_line = find_decl_name(
                match.group("name"), kind, len(declarations) + 1, clean_lines, idx
            )
            private = "private" in modifiers or "local" in modifiers
            if include_private or not private:
                declarations.append(
                    Declaration(
                        name=qualify_name(short_name, scopes),
                        short_name=short_name,
                        kind=kind,
                        file=rel(path, ROOT),
                        line=name_line or idx,
                        documented=pending_doc is not None,
                        doc_line=pending_doc[0] if pending_doc else None,
                        private=private,
                        protected="protected" in modifiers,
                        unsafe="unsafe" in modifiers,
                        noncomputable="noncomputable" in modifiers,
                        attributes=tuple(dict.fromkeys(pending_attrs)),
                        modifiers=modifiers,
                    )
                )
            pending_doc = None
            pending_attrs.clear()
            continue

        if stripped_clean and not stripped_original.startswith("--"):
            pending_doc = None
            pending_attrs.clear()

    return declarations


def scan_file_audit(
    path: Path,
    declarations: list[Declaration],
    allow_hard_regex: tuple[re.Pattern[str], ...] = (),
    text: str | None = None,
) -> FileAudit:
    text = read_text(path) if text is None else text
    clean = strip_comments_preserve_lines(text, strip_strings=True)
    lines = text.splitlines()
    public_decls = [d for d in declarations if not d.private]
    doc_public = [d for d in public_decls if d.documented]
    return FileAudit(
        file=rel(path, ROOT),
        loc=len(lines),
        imports=len(import_modules(text)),
        declarations=len(declarations),
        public_declarations=len(public_decls),
        documented_public=len(doc_public),
        missing_doc_public=len(public_decls) - len(doc_public),
        sorry_tokens=len(re.findall(r"\bsorry\b", clean)),
        hard_placeholders=hard_placeholder_count(path, clean, allow_hard_regex),
        nolint_suppressions=len(NOLINT_RE.findall(clean)),
        todos=len(TODO_RE.findall(text)),
        longest_line=max((len(line) for line in lines), default=0),
    )


def selected_files(targets: list[str]) -> list[Path]:
    if targets:
        files = [path for raw in targets for path in resolve_target_files(raw, root=ROOT)]
    else:
        files = default_library_files(root=ROOT)
    return sorted(dict.fromkeys(path.resolve() for path in files))


def scan_file_bundle(path: Path, args: argparse.Namespace) -> tuple[list[Declaration], FileAudit]:
    text = read_text(path)
    decls = scan_declarations(path, include_private=args.include_private, text=text)
    audit = scan_file_audit(path, decls, tuple(args.allow_hard_regex), text=text)
    return decls, audit


def make_snapshot(declarations: list[Declaration], audits: list[FileAudit]) -> dict[str, object]:
    return {
        "version": 2,
        "root": ROOT.as_posix(),
        "declarations": [asdict(d) for d in sorted(declarations, key=lambda d: d.name)],
        "files": [asdict(a) for a in sorted(audits, key=lambda a: a.file)],
    }


def load_snapshot(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def decl_map(snapshot: dict[str, object]) -> dict[str, dict[str, object]]:
    return {str(d["name"]): d for d in snapshot.get("declarations", [])}  # type: ignore[index]


def print_diff(old_snapshot: dict[str, object], new_snapshot: dict[str, object], *, limit: int, fail_on_added: bool) -> int:
    old = decl_map(old_snapshot)
    new = decl_map(new_snapshot)
    old_names = set(old)
    new_names = set(new)
    added = sorted(new_names - old_names)
    removed = sorted(old_names - new_names)
    changed_kind = sorted(n for n in old_names & new_names if old[n].get("kind") != new[n].get("kind"))
    doc_changed = sorted(n for n in old_names & new_names if old[n].get("documented") != new[n].get("documented"))

    print("== API diff ==")
    print(f"added: {len(added)}")
    for name in added[:limit]:
        d = new[name]
        print(f"  + {name} [{d.get('kind')}] {d.get('file')}:{d.get('line')}")
    if len(added) > limit:
        print(f"  ... {len(added) - limit} more")
    print(f"removed: {len(removed)}")
    for name in removed[:limit]:
        d = old[name]
        print(f"  - {name} [{d.get('kind')}] {d.get('file')}:{d.get('line')}")
    if len(removed) > limit:
        print(f"  ... {len(removed) - limit} more")
    print(f"kind changes: {len(changed_kind)}")
    for name in changed_kind[:limit]:
        print(f"  * {name}: {old[name].get('kind')} -> {new[name].get('kind')}")
    print(f"doc coverage changes: {len(doc_changed)}")
    for name in doc_changed[:limit]:
        print(f"  * {name}: documented {old[name].get('documented')} -> {new[name].get('documented')}")
    if removed or changed_kind or (fail_on_added and added):
        return 1
    return 0


def markdown_report(declarations: list[Declaration], audits: list[FileAudit], require_docs: set[str], limit: int) -> str:
    public = [d for d in declarations if not d.private]
    missing = [d for d in public if d.kind in require_docs and not d.documented]
    kind_counts = Counter(d.kind for d in public)
    hard_files = sorted(audits, key=lambda a: (a.sorry_tokens + a.hard_placeholders + a.nolint_suppressions, a.loc), reverse=True)
    lines: list[str] = []
    lines.append("# Lean public API audit")
    lines.append("")
    lines.append(f"Public declarations: {len(public)}")
    lines.append(f"Declarations missing required documentation: {len(missing)}")
    lines.append("")
    lines.append("## Public declaration kinds")
    lines.append("")
    lines.append("| kind | count |")
    lines.append("|---|---:|")
    for kind, count in sorted(kind_counts.items()):
        lines.append(f"| `{kind}` | {count} |")
    lines.append("")
    lines.append("## Missing documentation")
    lines.append("")
    if not missing:
        lines.append("None.")
    else:
        lines.append("| declaration | kind | location |")
        lines.append("|---|---|---|")
        for d in missing[:limit]:
            lines.append(f"| `{d.name}` | `{d.kind}` | `{d.file}:{d.line}` |")
        if len(missing) > limit:
            lines.append(f"| ... | ... | {len(missing) - limit} more |")
    lines.append("")
    lines.append("## Files needing attention")
    lines.append("")
    lines.append("| file | loc | missing docs | sorry | hard | nolint | TODO |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|")
    for a in hard_files[:limit]:
        if not (a.missing_doc_public or a.sorry_tokens or a.hard_placeholders or a.nolint_suppressions or a.todos):
            continue
        lines.append(
            f"| `{a.file}` | {a.loc} | {a.missing_doc_public} | {a.sorry_tokens} | {a.hard_placeholders} | {a.nolint_suppressions} | {a.todos} |"
        )
    return "\n".join(lines) + "\n"


def print_summary(declarations: list[Declaration], audits: list[FileAudit], require_docs: set[str], limit: int) -> tuple[int, int]:
    public = [d for d in declarations if not d.private]
    missing = [d for d in public if d.kind in require_docs and not d.documented]
    kind_counts = Counter(d.kind for d in public)
    attr_counts = Counter(attr for d in public for attr in d.attributes)
    duplicate_names = [name for name, count in Counter(d.name for d in public).items() if count > 1]
    totals = {
        "files": len(audits),
        "loc": sum(a.loc for a in audits),
        "imports": sum(a.imports for a in audits),
        "public_declarations": len(public),
        "missing_required_docs": len(missing),
        "duplicate_static_names": len(duplicate_names),
        "sorry_tokens": sum(a.sorry_tokens for a in audits),
        "hard_placeholders": sum(a.hard_placeholders for a in audits),
        "nolint_suppressions": sum(a.nolint_suppressions for a in audits),
        "todos": sum(a.todos for a in audits),
    }
    print("== public API audit ==")
    for key, value in totals.items():
        print(f"{key}: {value}")
    print("\n== public declaration kinds ==")
    for kind, count in sorted(kind_counts.items()):
        print(f"{kind}: {count}")
    if attr_counts:
        print("\n== frequent attributes ==")
        for attr, count in attr_counts.most_common(20):
            print(f"{attr}: {count}")
    print("\n== missing required docs ==")
    if not missing:
        print("none")
    for d in missing[:limit]:
        print(f"MISSING-DOC {d.file}:{d.line}: {d.kind} {d.name}")
    if len(missing) > limit:
        print(f"... {len(missing) - limit} more")
    if duplicate_names:
        print("\n== duplicate static declaration names ==")
        for name in duplicate_names[:limit]:
            print(f"DUPLICATE-NAME {name}")
    print("\n== risk files ==")
    risky = sorted(
        audits,
        key=lambda a: (a.sorry_tokens, a.hard_placeholders, a.nolint_suppressions, a.missing_doc_public, a.todos, a.loc),
        reverse=True,
    )
    for a in risky[:limit]:
        if a.sorry_tokens or a.hard_placeholders or a.nolint_suppressions or a.missing_doc_public or a.todos:
            print(
                f"{a.file}: loc={a.loc} missing-doc={a.missing_doc_public} sorry={a.sorry_tokens} "
                f"hard={a.hard_placeholders} nolint={a.nolint_suppressions} TODO={a.todos}"
            )
    return len(missing), totals["hard_placeholders"] + totals["sorry_tokens"]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit and snapshot public Lean API surface.")
    parser.add_argument("targets", nargs="*", help="Lean files, directories, or modules; default is local Lean4 library")
    parser.add_argument("--include-private", action="store_true")
    parser.add_argument("--require-docs", nargs="*", default=list(DEFAULT_REQUIRE_DOCS), help="declaration kinds that must have docstrings")
    parser.add_argument("--snapshot", help="write a JSON API snapshot")
    parser.add_argument("--diff", help="compare against an existing JSON API snapshot")
    parser.add_argument("--fail-on-added", action="store_true", help="with --diff, fail on newly added public API too")
    parser.add_argument("--markdown", help="write a Markdown audit report")
    parser.add_argument("--json", action="store_true", help="print JSON snapshot to stdout")
    parser.add_argument("--limit", type=int, default=80)
    parser.add_argument("--jobs", type=int, default=1, help="parallel static file scans")
    parser.add_argument("--fail-on-missing-docs", action="store_true")
    parser.add_argument("--fail-on-hard", action="store_true", help="fail if sorry/axiom/opaque/admit style hard placeholders remain")
    parser.add_argument(
        "--allow-hard-regex",
        action="append",
        type=re.compile,
        default=[],
        help="ignore hard-placeholder matches whose location or line text matches this regex",
    )
    args = parser.parse_args(argv)

    files = selected_files(args.targets)
    declarations: list[Declaration] = []
    audits: list[FileAudit] = []
    for decls, audit in map_with_jobs(files, lambda path: scan_file_bundle(path, args), jobs=args.jobs):
        declarations.extend(decls)
        audits.append(audit)

    snapshot = make_snapshot(declarations, audits)
    require_docs = set(args.require_docs or [])
    missing_count, hard_count = print_summary(declarations, audits, require_docs, args.limit)

    diff_exit = 0
    if args.diff:
        diff_exit = print_diff(load_snapshot(Path(args.diff)), snapshot, limit=args.limit, fail_on_added=args.fail_on_added)
    if args.snapshot:
        write_json_file(Path(args.snapshot), snapshot)
    if args.markdown:
        Path(args.markdown).write_text(markdown_report(declarations, audits, require_docs, args.limit), encoding="utf-8")
    if args.json:
        print(json_dump(snapshot))

    if diff_exit:
        return diff_exit
    if args.fail_on_missing_docs and missing_count:
        return 1
    if args.fail_on_hard and hard_count:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
