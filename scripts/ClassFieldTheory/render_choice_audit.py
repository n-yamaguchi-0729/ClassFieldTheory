#!/usr/bin/env python3
"""Render the human-readable public-choice audit from its checked manifest."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

from source_layout import DOCS_ROOT


MANIFEST = DOCS_ROOT / "choice-audit.json"
OUTPUT = DOCS_ROOT / "choice-audit.md"


def cell(value: object) -> str:
    if isinstance(value, list):
        return "<br>".join(f"`{item}`" for item in value) if value else "—"
    text = str(value or "—")
    return text.replace("|", "\\|").replace("\n", " ")


def boundary(entry: dict[str, object]) -> str:
    classification = entry.get("classification")
    if classification != "essentially_chosen":
        return "choice erased"
    if entry.get("choice_visible") is True:
        return "reviewed `choice_visible` legacy name"
    return "`chosen`/`choice` name marker"


def render(manifest: dict[str, object]) -> str:
    declarations = manifest["declarations"]
    assert isinstance(declarations, list)
    derived = manifest.get("derived_declarations", [])
    assert isinstance(derived, list)
    source = manifest["source_inventory"]
    assert isinstance(source, dict)
    module_count = source["module_count"]
    assert isinstance(module_count, int)
    objects = [entry for entry in declarations if entry.get("role") == "object"]
    proofs = len(declarations) - len(objects)
    primitives = [str(item) for item in manifest["choice_primitives"]]
    primitive_counts = Counter(
        primitive
        for entry in declarations
        for primitive in entry.get("uses", [])
    )
    classifications = Counter(str(entry.get("classification")) for entry in objects)
    derived_classifications = Counter(
        str(entry.get("classification")) for entry in derived
    )
    primitive_summary = ", ".join(
        f"`{primitive}`: {primitive_counts[primitive]}" for primitive in primitives
    )
    classification_summary = ", ".join(
        f"`{name}`: {classifications[name]}"
        for name in ("internal_choice", "result_canonical", "essentially_chosen")
    )
    derived_classification_summary = ", ".join(
        f"`{name}`: {derived_classifications[name]}"
        for name in ("internal_choice", "result_canonical", "essentially_chosen")
    )

    lines = [
        "# Public choice audit",
        "",
        "This document records the public choice boundary of the Class Field Theory",
        "library. The",
        "authoritative, CI-checked inventory is [`choice-audit.json`](choice-audit.json).",
        "It lists every syntactically public declaration whose own command directly",
        "uses an audited choice primitive, plus public value declarations with an",
        "explicit `chosen` boundary or a manually reviewed derived-choice contract.",
        "Comments, strings, theorem bodies, and proof-only dependencies do not taint",
        "derived public values.",
        "",
        f"The checked source inventory contains **{module_count} Lean modules**.",
        "",
        f"The current inventory contains **{len(declarations)} declarations**:",
        f"**{len(objects)} object-producing declarations** and **{proofs} proof-only",
        "theorem/lemma implementations**. Primitive counts are " + primitive_summary + ".",
        f"The derived inventory contains **{len(derived)} reviewed value declarations**.",
        "",
        "## Classification contract",
        "",
        "- `internal_choice`: proof-valued or observationally irrelevant data; the listed",
        "  independence declaration explains why the choice cannot affect the result.",
        "- `result_canonical`: the implementation chooses a witness, but public",
        "  uniqueness/independence theorems characterize the result.",
        "- `essentially_chosen`: callers can observe the selected witness/equivalence/",
        "  section. The name must explicitly contain `choice` or `chosen`, or the object",
        "  must be confined to an `Internal` namespace. Existing unmarked public",
        "  boundaries are frozen individually with `choice_visible: true`; this flag",
        "  cannot approve a newly discovered object because the initializer checks the",
        "  complete reviewed name partition.",
        "",
        "Current object totals are " + classification_summary + ".",
        "Derived-value totals are " + derived_classification_summary + ".",
        "",
        "## Static gate",
        "",
        "```text",
        "python3 scripts/ClassFieldTheory/check_choice_contract.py",
        "python3 scripts/ClassFieldTheory/check_choice_contract.py --self-test",
        "python3 scripts/ClassFieldTheory/render_choice_audit.py --check",
        "```",
        "",
        "The checker rejects an unreviewed or stale declaration; missing or stale",
        "witness/specification/independence references; an unmarked essential choice; an unreviewed public",
        "`Quotient.out` object; and the removed representative-exposing ZHat/coset APIs.",
        "The renderer makes this prose view reproducible from the reviewed JSON rather",
        "than maintaining a second hand-written inventory.",
        "",
        "## Curated public objects",
        "",
        "| declaration | primitive | classification | public boundary | witness/source | specification | independence/uniqueness | rationale |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for entry in sorted(objects, key=lambda item: str(item.get("name", ""))):
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{entry['name']}`",
                    cell(entry.get("uses", [])),
                    f"`{entry['classification']}`",
                    boundary(entry),
                    cell(entry.get("witness", [])),
                    cell(entry.get("spec", [])),
                    cell(entry.get("independence", [])),
                    cell(entry.get("note", "")),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Derived chosen-value boundaries",
            "",
            "| declaration | classification | chosen dependencies | detection | witness/source | specification | independence/uniqueness | rationale |",
            "|---|---|---|---|---|---|---|---|",
        ]
    )
    for entry in sorted(derived, key=lambda item: str(item.get("name", ""))):
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{entry['name']}`",
                    f"`{entry['classification']}`",
                    cell(entry.get("depends_on", [])),
                    cell(entry.get("detection", [])),
                    cell(entry.get("witness", [])),
                    cell(entry.get("spec", [])),
                    cell(entry.get("independence", [])),
                    cell(entry.get("note", "")),
                )
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    try:
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(
            f"choice-audit-render: manifest is missing: {args.manifest}",
            file=sys.stderr,
        )
        return 2
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(
            f"choice-audit-render: cannot read {args.manifest}: {error}",
            file=sys.stderr,
        )
        return 2
    if not isinstance(manifest, dict):
        print("choice-audit-render: manifest root must be an object", file=sys.stderr)
        return 2
    source = manifest.get("source_inventory")
    declarations = manifest.get("declarations")
    derived = manifest.get("derived_declarations")
    if (
        manifest.get("schema_version") != 3
        or not isinstance(source, dict)
        or isinstance(source.get("module_count"), bool)
        or not isinstance(source.get("module_count"), int)
        or not isinstance(declarations, list)
        or not all(isinstance(entry, dict) for entry in declarations)
        or not isinstance(derived, list)
        or not all(isinstance(entry, dict) for entry in derived)
        or not isinstance(manifest.get("choice_primitives"), list)
    ):
        print(
            "choice-audit-render: manifest schema/content is invalid; "
            "run check_choice_contract.py first",
            file=sys.stderr,
        )
        return 2
    expected = render(manifest)
    if args.check:
        actual = (
            args.output.read_text(encoding="utf-8")
            if args.output.exists()
            else ""
        )
        if actual != expected:
            print(
                f"choice-audit-render: FAILED: {args.output} is missing/stale; "
                "run render_choice_audit.py",
                file=sys.stderr,
            )
            return 1
        print("choice-audit-render: OK")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(expected, encoding="utf-8")
    temporary.replace(args.output)
    print(f"choice-audit-render: wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
