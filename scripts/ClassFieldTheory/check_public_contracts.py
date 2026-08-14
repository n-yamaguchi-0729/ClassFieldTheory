#!/usr/bin/env python3
"""Run source-independent Class Field Theory maintenance checks.

Reviewed choice, architecture, and performance records are established
separately once the reorganized source tree is stable.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[1]


def main() -> int:
    checks = (
        (
            "source policy checker self-test",
            [HERE / "check_source_policy.py", "--self-test"],
        ),
        ("source policy", [HERE / "check_source_policy.py"]),
        (
            "documentation checker self-test",
            [HERE / "check_documentation_contract.py", "--self-test"],
        ),
        ("documentation", [HERE / "check_documentation_contract.py"]),
        (
            "public object documentation",
            [
                HERE.parent / "lean_public_api.py",
                WORKSPACE / "Lean4" / "ClassFieldTheory",
                "--require-docs",
                "def",
                "structure",
                "class",
                "inductive",
                "abbrev",
                "--fail-on-missing-docs",
                "--limit",
                "0",
            ],
        ),
        (
            "architecture checker self-test",
            [HERE / "check_architecture_contract.py", "--self-test"],
        ),
        (
            "architecture",
            [HERE / "check_architecture_contract.py"],
        ),
        ("choice checker self-test", [HERE / "check_choice_contract.py", "--self-test"]),
        ("choice contract", [HERE / "check_choice_contract.py"]),
        (
            "choice audit rendering",
            [HERE / "render_choice_audit.py", "--check"],
        ),
        ("finite cardinality", [HERE / "check_nat_card_contract.py"]),
        (
            "performance checker self-test",
            [HERE / "check_performance_contract.py", "--self-test"],
        ),
        (
            "declaration tower scanner self-test",
            [HERE / "audit_declaration_towers.py", "--self-test"],
        ),
        (
            "static declaration performance",
            [HERE / "check_performance_contract.py", "--static-only"],
        ),
        (
            "frontier builder self-test",
            [HERE / "build_nongreen_frontier.py", "--self-test"],
        ),
        (
            "green freshness self-test",
            [HERE / "green_status.py", "--self-test"],
        ),
    )
    failed: list[str] = []
    for label, command in checks:
        print(f"public-contracts: running {label}", flush=True)
        try:
            completed = subprocess.run(
                [sys.executable, *(str(part) for part in command)],
                check=False,
            )
        except OSError as error:
            print(
                f"public-contracts: cannot run {label}: {error}",
                file=sys.stderr,
            )
            failed.append(label)
            continue
        if completed.returncode != 0:
            failed.append(label)
    if failed:
        print(
            "public-contracts: FAILED: " + ", ".join(failed),
            file=sys.stderr,
        )
        return 1
    print("public-contracts: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
