#!/usr/bin/env python3
"""Static source-layout, import-graph, and metric contract for ClassFieldTheory.

Every physical production source directory has a same-named aggregate.  Each
aggregate directly imports every immediate child module and transitively
reaches its complete subtree.  The production graph is acyclic and completely
reachable from ``ClassFieldTheory``.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
import tomllib
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from graphlib import CycleError, TopologicalSorter
from pathlib import Path

from source_layout import (
    CANONICAL_ROOT,
    DOCS_ROOT,
    LEAN_ROOT,
    WORKSPACE_ROOT,
    contract_source_files,
    lean_code_line_count,
    source_inventory,
    source_relative_path,
    strip_lean_comments,
)


DEFAULT_BASELINE = DOCS_ROOT / "architecture-metrics.json"
LAKEFILE = WORKSPACE_ROOT / "lakefile.toml"
SCHEMA_VERSION = 4
MAX_PHYSICAL_LINES = 3000
# ClassFieldTheory may depend externally only on Mathlib. Every other import
# must resolve to a module owned by the production library.
EXTERNAL_IMPORT_PREFIXES = ("Mathlib",)
IGNORED_PHYSICAL_DIRECTORY_NAMES = frozenset({".lake", "__pycache__"})


@dataclass(frozen=True)
class PhysicalDirectoryFacts:
    """Lean-source density facts for one non-cache physical directory."""

    parts: tuple[str, ...]
    is_empty: bool
    direct_subdirectories: tuple[tuple[str, ...], ...]
    direct_lean_files: tuple[tuple[str, ...], ...]
    subtree_lean_files: tuple[tuple[str, ...], ...]


CANONICAL_SUBSYSTEM_IMPORTS = (
    "ValuationTheory",
    "GroupTheory",
    "LocalFieldTheory",
    "RamificationTheory",
    "LubinTate",
    "CyclicCohomology",
    "KummerTheory",
    "AbstractClassFieldTheory",
    "AlgebraicNumberTheory",
    "LocalClassFieldTheory",
    "KroneckerWeber",
    "HasseArf",
    "GlobalClassFieldTheory",
)

CANONICAL_IMPORTS = CANONICAL_SUBSYSTEM_IMPORTS

PRODUCTION_LIBRARY_NAME = "ClassFieldTheory"
PRODUCTION_LIBRARY_SRC_DIR = "Lean4"
EXPECTED_PRODUCTION_LIBRARY_GLOBS = ("ClassFieldTheory",)
PRODUCTION_CORE_LIBRARY_NAME = "ClassFieldTheoryCore"
PRODUCTION_CORE_LIBRARY_SRC_DIR = "Lean4/ClassFieldTheory"

PUBLIC_ROOTS = (
    "ClassFieldTheory",
    "ValuationTheory",
    "LocalFieldTheory",
    "RamificationTheory",
    "LubinTate",
    "CyclicCohomology",
    "KummerTheory",
    "AbstractClassFieldTheory",
    "AlgebraicNumberTheory",
    "LocalClassFieldTheory",
    "LocalClassFieldTheory.Finite.LocalReciprocity",
    "LocalClassFieldTheory.Finite.Existence",
    "LocalClassFieldTheory.Finite.Conductor",
    "LocalClassFieldTheory.Finite.UnramifiedConductor",
    "LocalClassFieldTheory.Infinite",
    "LocalClassFieldTheory.Kummer",
    "LocalClassFieldTheory.LubinTateApplication",
    "HasseArf",
    "KroneckerWeber",
    "GlobalClassFieldTheory",
)

METRIC_PATTERNS = {
    "classical_choose": re.compile(r"\bClassical\.(?:choose|choice)\b"),
    "deprecated_attributes": re.compile(r"@\[[^\]]*\bdeprecated\b"),
    "letI": re.compile(r"\bletI\b"),
    "quotient_out": re.compile(r"\bQuotient\.out\b"),
    "simp_attributes": re.compile(r"@\[[^\]]*\bsimp\b"),
    "type_zero": re.compile(r"\bType\s+0\b"),
}

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$", re.MULTILINE)


def module_name(path: Path) -> str:
    return Path(source_relative_path(path)).with_suffix("").as_posix().replace(
        "/", "."
    )


def module_path(module: str) -> Path:
    if module == "ClassFieldTheory":
        return CANONICAL_ROOT
    return LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


def check_lake_glob_exact_cover(
    library_name: str,
    raw_globs: object,
    source_root: Path,
    modules: set[str],
    errors: list[str],
) -> None:
    """Check that Lake globs cover each owned module exactly once.

    The Class Field Theory libraries use only literal module globs and Lake's
    recursive ``X.+`` form.  Requiring every glob to match a source module is
    important in addition to set equality: otherwise a stale recursive glob
    such as ``HasseArf.+`` could remain silently after its directory vanished.
    """

    if not isinstance(raw_globs, list) or not all(
        isinstance(glob, str) for glob in raw_globs
    ):
        errors.append(f"Lake library {library_name} globs must be a string array")
        return

    globs = tuple(raw_globs)
    if len(globs) != len(set(globs)):
        errors.append(f"Lake library {library_name} contains duplicate globs")

    coverage: Counter[str] = Counter()
    for glob in globs:
        matched: set[str]
        if glob.endswith(".+"):
            namespace = glob[:-2]
            if not namespace or any(character in namespace for character in "*+"):
                errors.append(
                    f"Lake library {library_name} has invalid recursive glob: {glob!r}"
                )
                continue
            directory = source_root.joinpath(*namespace.split("."))
            if not directory.is_dir():
                errors.append(
                    f"Lake library {library_name} recursive glob {glob!r} "
                    f"has no source directory: {directory}"
                )
            prefix = namespace + "."
            matched = {module for module in modules if module.startswith(prefix)}
            if not matched:
                errors.append(
                    f"Lake library {library_name} recursive glob {glob!r} "
                    "has no descendant modules"
                )
        elif "*" in glob or "+" in glob:
            errors.append(
                f"Lake library {library_name} uses unsupported glob syntax: {glob!r}"
            )
            continue
        else:
            matched = {glob} & modules
            if not matched:
                errors.append(
                    f"Lake library {library_name} literal glob {glob!r} "
                    "does not name an owned module"
                )
        coverage.update(matched)

    missing = sorted(modules - set(coverage))
    multiply_covered = sorted(
        module for module, count in coverage.items() if count != 1
    )
    if missing:
        errors.append(
            f"Lake library {library_name} globs miss owned modules: {missing!r}"
        )
    if multiply_covered:
        errors.append(
            f"Lake library {library_name} globs cover modules more than once: "
            f"{multiply_covered!r}"
        )


def check_lake_topology(
    production_files: list[Path],
    errors: list[str],
    lakefile: Path = LAKEFILE,
) -> None:
    """Validate the production ``lean_lib`` in ``lakefile.toml``."""

    try:
        with lakefile.open("rb") as handle:
            document = tomllib.load(handle)
    except FileNotFoundError:
        errors.append(f"Lake configuration is missing: {lakefile}")
        return
    except (OSError, tomllib.TOMLDecodeError) as error:
        errors.append(f"cannot parse Lake configuration {lakefile}: {error}")
        return

    raw_libraries = document.get("lean_lib")
    if not isinstance(raw_libraries, list):
        errors.append("Lake configuration lean_lib entries must be an array of tables")
        return
    libraries: list[dict[str, object]] = []
    for index, library in enumerate(raw_libraries):
        if not isinstance(library, dict):
            errors.append(f"Lake lean_lib entry {index} must be a table")
            continue
        libraries.append(library)

    def unique_library(name: str) -> dict[str, object] | None:
        matches = [library for library in libraries if library.get("name") == name]
        if len(matches) != 1:
            errors.append(
                f"Lake configuration must define exactly one {name} library; "
                f"found {len(matches)}"
            )
            return None
        return matches[0]

    production = unique_library(PRODUCTION_LIBRARY_NAME)
    production_core = unique_library(PRODUCTION_CORE_LIBRARY_NAME)
    if production is not None:
        if production.get("srcDir") != PRODUCTION_LIBRARY_SRC_DIR:
            errors.append(
                f"Lake library {PRODUCTION_LIBRARY_NAME} srcDir is "
                f"{production.get('srcDir')!r}; expected "
                f"{PRODUCTION_LIBRARY_SRC_DIR!r}"
            )
        raw_production_globs = production.get("globs")
        actual_production_globs = (
            tuple(raw_production_globs)
            if isinstance(raw_production_globs, list)
            and all(isinstance(glob, str) for glob in raw_production_globs)
            else None
        )
        if actual_production_globs != EXPECTED_PRODUCTION_LIBRARY_GLOBS:
            errors.append(
                f"Lake library {PRODUCTION_LIBRARY_NAME} globs are "
                f"{actual_production_globs!r}; expected "
                f"{EXPECTED_PRODUCTION_LIBRARY_GLOBS!r}"
            )
        check_lake_glob_exact_cover(
            PRODUCTION_LIBRARY_NAME,
            raw_production_globs,
            CANONICAL_ROOT.parent,
            {module_name(CANONICAL_ROOT)},
            errors,
        )
    if production_core is not None:
        if production_core.get("srcDir") != PRODUCTION_CORE_LIBRARY_SRC_DIR:
            errors.append(
                f"Lake library {PRODUCTION_CORE_LIBRARY_NAME} srcDir is "
                f"{production_core.get('srcDir')!r}; expected "
                f"{PRODUCTION_CORE_LIBRARY_SRC_DIR!r}"
            )
        check_lake_glob_exact_cover(
            PRODUCTION_CORE_LIBRARY_NAME,
            production_core.get("globs"),
            LEAN_ROOT,
            {
                module_name(path)
                for path in production_files
                if path != CANONICAL_ROOT
            },
            errors,
        )
    extra_libraries = [
        library.get("name")
        for library in libraries
        if library.get("name")
        not in {PRODUCTION_LIBRARY_NAME, PRODUCTION_CORE_LIBRARY_NAME}
    ]
    if extra_libraries:
        errors.append(
            "public Lake configuration must define only the production root and "
            "core ownership libraries; "
            f"extra entries: {extra_libraries!r}"
        )

    default_targets = document.get("defaultTargets")
    if not isinstance(default_targets, list) or not all(
        isinstance(target, str) for target in default_targets
    ):
        errors.append("Lake defaultTargets must be a string array")
    else:
        if PRODUCTION_LIBRARY_NAME not in default_targets:
            errors.append(
                f"Lake defaultTargets must include {PRODUCTION_LIBRARY_NAME}"
            )
@lru_cache(maxsize=None)
def imports(path: Path) -> tuple[str, ...]:
    text = strip_lean_comments(
        path.read_text(encoding="utf-8", errors="replace")
    )
    return tuple(IMPORT_RE.findall(text))


def internal_import_graph(files: list[Path]) -> dict[str, tuple[str, ...]]:
    owned = {module_name(path) for path in files}
    return {
        module_name(path): tuple(
            imported for imported in imports(path) if imported in owned
        )
        for path in files
    }


def transitive_import_closure(
    graph: dict[str, tuple[str, ...]],
    root: str,
    cache: dict[str, frozenset[str]] | None = None,
) -> frozenset[str]:
    if cache is not None and root in cache:
        return cache[root]
    seen: set[str] = set()
    pending = list(graph.get(root, ()))
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        pending.extend(graph.get(module, ()))
    result = frozenset(seen)
    if cache is not None:
        cache[root] = result
    return result


def internal_import_closures(
    files: list[Path],
    graph: dict[str, tuple[str, ...]] | None = None,
) -> dict[str, int]:
    selected_graph = graph if graph is not None else internal_import_graph(files)
    cache: dict[str, frozenset[str]] = {}
    return {
        root: len(transitive_import_closure(selected_graph, root, cache))
        for root in PUBLIC_ROOTS
    }


def unresolved_local_imports(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
) -> list[tuple[str, str]]:
    owned = set(graph)
    unresolved: list[tuple[str, str]] = []
    for path in files:
        owner = module_name(path)
        for imported in imports(path):
            if imported in owned:
                continue
            top_level = imported.split(".", 1)[0]
            if top_level not in EXTERNAL_IMPORT_PREFIXES:
                unresolved.append((owner, imported))
    return sorted(unresolved)


def import_cycle(
    graph: dict[str, tuple[str, ...]],
) -> tuple[str, ...] | None:
    try:
        tuple(TopologicalSorter(graph).static_order())
    except CycleError as error:
        if len(error.args) > 1 and isinstance(error.args[1], list):
            return tuple(str(module) for module in error.args[1])
        return (str(error),)
    return None


def ignored_physical_directory(name: str) -> bool:
    """Whether a generated cache directory is outside the physical contract."""

    return (
        name in IGNORED_PHYSICAL_DIRECTORY_NAMES
        or (name.startswith(".") and "cache" in name.casefold())
    )


def physical_directory_facts(
    root: Path = LEAN_ROOT,
) -> tuple[PhysicalDirectoryFacts, ...]:
    """Return density facts for every physical non-cache directory below root."""

    resolved_root = root.resolve()
    direct_files: dict[
        tuple[str, ...], tuple[tuple[str, ...], ...]
    ] = {}
    direct_subdirectories: dict[
        tuple[str, ...], tuple[tuple[str, ...], ...]
    ] = {}
    empty_directories: set[tuple[str, ...]] = set()
    for current_name, directory_names, file_names in os.walk(resolved_root):
        directory_names[:] = sorted(
            name
            for name in directory_names
            if not ignored_physical_directory(name)
        )
        file_names.sort()
        current = Path(current_name)
        parts = current.relative_to(resolved_root).parts
        if not parts:
            continue
        direct_subdirectories[parts] = tuple(
            parts + (name,) for name in directory_names
        )
        direct_files[parts] = tuple(
            parts + (name,)
            for name in file_names
            if name.endswith(".lean")
        )
        if not directory_names and not file_names:
            empty_directories.add(parts)

    subtree_files: dict[
        tuple[str, ...], list[tuple[str, ...]]
    ] = {parts: [] for parts in direct_files}
    for files in direct_files.values():
        for source in files:
            for depth in range(1, len(source)):
                ancestor = source[:depth]
                if ancestor in subtree_files:
                    subtree_files[ancestor].append(source)

    return tuple(
        PhysicalDirectoryFacts(
            parts=parts,
            is_empty=parts in empty_directories,
            direct_subdirectories=direct_subdirectories[parts],
            direct_lean_files=direct_files[parts],
            subtree_lean_files=tuple(subtree_files[parts]),
        )
        for parts in sorted(direct_files)
    )


def nested_lake_directories(root: Path) -> tuple[Path, ...]:
    """Return source-local Lake trees instead of the workspace artifact tree."""

    resolved_root = root.resolve()
    found: list[Path] = []
    for current_name, directory_names, _file_names in os.walk(resolved_root):
        current = Path(current_name)
        if ".lake" in directory_names:
            found.append((current / ".lake").relative_to(resolved_root))
        directory_names[:] = [
            name for name in directory_names if name != ".lake"
        ]
    return tuple(sorted(found))


def physical_layout_metrics(root: Path = LEAN_ROOT) -> dict[str, int]:
    facts = physical_directory_facts(root)
    return {
        "physical_directories": len(facts),
        "nested_lake_directories": len(nested_lake_directories(root)),
        "empty_directories": sum(fact.is_empty for fact in facts),
        "nonempty_zero_lean_directories": sum(
            not fact.is_empty and not fact.subtree_lean_files
            for fact in facts
        ),
        "one_child_zero_direct_lean_directories": sum(
            not fact.direct_lean_files
            and len(fact.direct_subdirectories) == 1
            for fact in facts
        ),
    }


def check_physical_layout(root: Path, errors: list[str]) -> None:
    for directory in nested_lake_directories(root):
        errors.append(
            "source-local Lake directory must use the workspace artifact "
            f"tree: {directory.as_posix()}"
        )
    facts = physical_directory_facts(root)
    for fact in facts:
        directory = "/".join(fact.parts)
        if fact.is_empty:
            errors.append(f"physical source directory is empty: {directory}")
        if (
            not fact.direct_lean_files
            and len(fact.direct_subdirectories) == 1
        ):
            child = "/".join(fact.direct_subdirectories[0])
            errors.append(
                "physical source directory has no direct Lean files and "
                f"exactly one child directory: {directory} -> {child}"
            )


def source_directories(files: list[Path]) -> list[tuple[str, ...]]:
    directories: set[tuple[str, ...]] = set()
    for path in files:
        if path == CANONICAL_ROOT:
            continue
        relative = path.relative_to(LEAN_ROOT)
        for depth in range(1, len(relative.parts)):
            directories.add(relative.parts[:depth])
    return sorted(directories)


def directory_module(parts: tuple[str, ...]) -> str:
    return ".".join(parts)


def module_scope(directory: str, modules: set[str]) -> set[str]:
    prefix = directory + "."
    return {
        module for module in modules
        if module == directory or module.startswith(prefix)
    }


def immediate_child_modules(directory: str, modules: set[str]) -> set[str]:
    """Return modules represented by direct Lean files in a directory."""

    prefix = directory + "."
    return {
        module
        for module in modules
        if module.startswith(prefix) and "." not in module[len(prefix):]
    }


def aggregate_contract_gaps(
    aggregate: str,
    graph: dict[str, tuple[str, ...]],
    cache: dict[str, frozenset[str]] | None = None,
) -> tuple[set[str], set[str]]:
    """Return missing immediate imports and missing subtree coverage."""

    modules = set(graph)
    missing_direct = immediate_child_modules(aggregate, modules) - set(
        graph.get(aggregate, ())
    )
    descendants = module_scope(aggregate, modules) - {aggregate}
    missing_descendants = descendants - set(
        transitive_import_closure(graph, aggregate, cache)
    )
    return missing_direct, missing_descendants


def directory_aggregation_metrics(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
) -> dict[str, object]:
    """Measure the exception-free physical aggregate contract."""

    modules = set(graph)
    cache: dict[str, frozenset[str]] = {}
    directories = source_directories(files)
    same_name_aggregates = 0
    direct_import_complete = 0
    subtree_import_complete = 0
    for parts in directories:
        directory = directory_module(parts)
        if directory not in modules:
            continue
        same_name_aggregates += 1
        missing_direct, missing_descendants = aggregate_contract_gaps(
            directory, graph, cache
        )
        if not missing_direct:
            direct_import_complete += 1
        if not missing_descendants:
            subtree_import_complete += 1
    return {
        "physical_owner_directories": len(directories),
        "same_name_aggregates": same_name_aggregates,
        "direct_import_complete": direct_import_complete,
        "subtree_import_complete": subtree_import_complete,
    }


def import_graph_metrics(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
) -> dict[str, object]:
    owned = set(graph)
    external_count = sum(
        1
        for path in files
        for imported in imports(path)
        if imported not in owned
    )
    root_coverage = {"ClassFieldTheory"}
    root_coverage.update(transitive_import_closure(graph, "ClassFieldTheory"))
    return {
        "internal_imports": sum(len(dependencies) for dependencies in graph.values()),
        "external_imports": external_count,
        "canonical_root_reachable_modules": len(root_coverage),
        "unresolved_local_imports": len(unresolved_local_imports(files, graph)),
        "self_imports": sum(
            module in dependencies for module, dependencies in graph.items()
        ),
        "acyclic": import_cycle(graph) is None,
    }


def compute_metrics(files: list[Path]) -> dict[str, object]:
    graph = internal_import_graph(files)
    counts: Counter[str] = Counter()
    file_metrics: list[dict[str, object]] = []
    for path in files:
        source = path.read_text(encoding="utf-8", errors="replace")
        code = strip_lean_comments(source)
        for name, pattern in METRIC_PATTERNS.items():
            counts[name] += len(pattern.findall(code))
        file_metrics.append(
            {
                "file": source_relative_path(path),
                "code_lines": lean_code_line_count(source),
                "physical_lines": len(source.splitlines()),
            }
        )

    file_metrics.sort(key=lambda item: str(item["file"]))
    largest = sorted(
        file_metrics,
        key=lambda item: (
            -int(item["code_lines"]),
            -int(item["physical_lines"]),
            str(item["file"]),
        ),
    )[:20]
    return {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": source_inventory(files),
        "lean_files": len(files),
        "code_lines": sum(int(item["code_lines"]) for item in file_metrics),
        "physical_lines": sum(
            int(item["physical_lines"]) for item in file_metrics
        ),
        "counts": dict(sorted(counts.items())),
        "internal_import_closure": internal_import_closures(files, graph),
        "import_graph": import_graph_metrics(files, graph),
        "physical_layout": physical_layout_metrics(),
        "directory_aggregation": directory_aggregation_metrics(files, graph),
        "files": file_metrics,
        "largest_files": largest,
    }


def architecture_baseline(metrics: dict[str, object]) -> dict[str, object]:
    raw_files = metrics["files"]
    assert isinstance(raw_files, list)
    return {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": metrics["source_inventory"],
        "count_ceilings": metrics["counts"],
        "internal_import_closure_ceilings": metrics[
            "internal_import_closure"
        ],
        "import_graph": metrics["import_graph"],
        "directory_aggregation": metrics["directory_aggregation"],
        "per_file_code_line_ceilings": {
            str(item["file"]): int(item["code_lines"])
            for item in raw_files
            if isinstance(item, dict)
        },
    }


def validate_ceiling_map(
    baseline: object,
    current: object,
    label: str,
    errors: list[str],
) -> None:
    if not isinstance(baseline, dict) or not isinstance(current, dict):
        errors.append(f"{label} must be an object")
        return
    if set(baseline) != set(current):
        missing = sorted(set(current) - set(baseline))
        stale = sorted(set(baseline) - set(current))
        if missing:
            errors.append(f"{label} is missing keys: {missing!r}")
        if stale:
            errors.append(f"{label} has stale keys: {stale!r}")
        return
    for key, value in current.items():
        ceiling = baseline.get(key)
        if (
            isinstance(value, bool)
            or not isinstance(value, int)
            or isinstance(ceiling, bool)
            or not isinstance(ceiling, int)
            or ceiling < value
        ):
            errors.append(
                f"{label}.{key} is {value!r}, above or incompatible with "
                f"ceiling {ceiling!r}"
            )


def validate_baseline(
    baseline: object,
    metrics: dict[str, object],
    errors: list[str],
) -> None:
    if not isinstance(baseline, dict):
        errors.append("architecture baseline root must be an object")
        return
    if baseline.get("schema_version") != SCHEMA_VERSION:
        errors.append(
            f"architecture baseline schema_version must be {SCHEMA_VERSION}"
        )
    if baseline.get("source_inventory") != metrics["source_inventory"]:
        errors.append(
            "architecture baseline source inventory differs from the current "
            "Class Field Theory source tree"
        )
    validate_ceiling_map(
        baseline.get("count_ceilings"),
        metrics.get("counts"),
        "count_ceilings",
        errors,
    )
    validate_ceiling_map(
        baseline.get("internal_import_closure_ceilings"),
        metrics.get("internal_import_closure"),
        "internal_import_closure_ceilings",
        errors,
    )
    for label in ("import_graph", "directory_aggregation"):
        if baseline.get(label) != metrics.get(label):
            errors.append(
                f"architecture baseline {label} differs from the current "
                "Class Field Theory source tree"
            )
    current_files = metrics.get("files")
    file_lines = {
        str(item["file"]): int(item["code_lines"])
        for item in current_files
        if isinstance(current_files, list) and isinstance(item, dict)
    }
    validate_ceiling_map(
        baseline.get("per_file_code_line_ceilings"),
        file_lines,
        "per_file_code_line_ceilings",
        errors,
    )


def check_directory_aggregation(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
    errors: list[str],
) -> None:
    modules = set(graph)
    cache: dict[str, frozenset[str]] = {}
    for parts in source_directories(files):
        directory = directory_module(parts)
        if directory not in modules:
            errors.append(
                f"source directory lacks same-name aggregate: {directory}"
            )
            continue
        missing_direct, missing_descendants = aggregate_contract_gaps(
            directory, graph, cache
        )
        if missing_descendants:
            errors.append(
                f"directory aggregate {directory} misses descendants: "
                f"{sorted(missing_descendants)!r}"
            )
        if missing_direct:
            errors.append(
                f"directory aggregate {directory} misses direct children: "
                f"{sorted(missing_direct)!r}"
            )


def check_import_graph(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
    errors: list[str],
) -> None:
    for owner, imported in unresolved_local_imports(files, graph):
        errors.append(f"unresolved local import: {owner} imports {imported}")
    for module, dependencies in graph.items():
        if module in dependencies:
            errors.append(f"module imports itself: {module}")
    cycle = import_cycle(graph)
    if cycle is not None:
        errors.append(f"internal import cycle: {' -> '.join(cycle)}")
    root_coverage = {"ClassFieldTheory"}
    root_coverage.update(transitive_import_closure(graph, "ClassFieldTheory"))
    missing = sorted(set(graph) - root_coverage)
    if missing:
        errors.append(
            f"canonical root reaches {len(root_coverage)} / {len(graph)} "
            f"owned modules; missing: {missing!r}"
        )


def check_layout(
    files: list[Path],
    graph: dict[str, tuple[str, ...]],
    errors: list[str],
) -> None:
    check_lake_topology(files, errors)
    check_physical_layout(LEAN_ROOT, errors)
    if files[0] != CANONICAL_ROOT:
        errors.append("canonical root is not first in the source inventory")
    if imports(CANONICAL_ROOT) != CANONICAL_IMPORTS:
        errors.append(
            f"{CANONICAL_ROOT.name} imports {imports(CANONICAL_ROOT)!r}; "
            f"expected {CANONICAL_IMPORTS!r}"
        )
    modules = [module_name(path) for path in files]
    if len(modules) != len(set(modules)):
        errors.append("multiple source files resolve to the same Lean module")
    for path in files:
        physical_lines = len(
            path.read_text(encoding="utf-8", errors="replace").splitlines()
        )
        if physical_lines > MAX_PHYSICAL_LINES:
            errors.append(
                f"{source_relative_path(path)} has {physical_lines} physical "
                f"lines; limit is {MAX_PHYSICAL_LINES}"
            )
    for root in PUBLIC_ROOTS:
        if not module_path(root).is_file():
            errors.append(f"public root module is missing: {root}")
    check_import_graph(files, graph, errors)
    check_directory_aggregation(files, graph, errors)


def run_self_tests() -> None:
    source = '''/- module documentation
  /- nested comment -/
-/

def visible := "-- is part of this string" -- trailing comment
/- comment-only line -/
theorem kept : True := by
  trivial
'''
    assert lean_code_line_count(source) == 3
    stripped = strip_lean_comments(source)
    assert "module documentation" not in stripped
    assert '"-- is part of this string"' in stripped

    with tempfile.TemporaryDirectory() as temporary_name:
        source_root = Path(temporary_name) / "Source"
        (source_root / "Root").mkdir(parents=True)
        modules = {"Root", "Root.Child"}
        errors: list[str] = []
        check_lake_glob_exact_cover(
            "Synthetic",
            ["Root", "Root.+"],
            source_root,
            modules,
            errors,
        )
        assert not errors, errors
        stale_errors: list[str] = []
        check_lake_glob_exact_cover(
            "Synthetic",
            ["Root", "Root.+", "Missing.+"],
            source_root,
            modules,
            stale_errors,
        )
        assert any(
            "recursive glob 'Missing.+' has no source directory" in error
            for error in stale_errors
        ), stale_errors
        assert any(
            "recursive glob 'Missing.+' has no descendant modules" in error
            for error in stale_errors
        ), stale_errors

    with tempfile.TemporaryDirectory() as temporary_name:
        root = Path(temporary_name)
        (root / "Empty").mkdir()
        errors = []
        check_physical_layout(root, errors)
        assert errors == ["physical source directory is empty: Empty"], errors

    with tempfile.TemporaryDirectory() as temporary_name:
        root = Path(temporary_name)
        nested = root / "Chain" / "Middle" / "Nested"
        nested.mkdir(parents=True)
        (nested / "Only.lean").write_text("def only := 1\n", encoding="utf-8")
        errors = []
        check_physical_layout(root, errors)
        assert errors == [
            "physical source directory has no direct Lean files and exactly "
            "one child directory: Chain -> Chain/Middle",
            "physical source directory has no direct Lean files and exactly "
            "one child directory: Chain/Middle -> Chain/Middle/Nested",
        ], errors

    with tempfile.TemporaryDirectory() as temporary_name:
        root = Path(temporary_name)
        nested = root / "Outer" / "Inner"
        nested.mkdir(parents=True)
        (nested / "Left.lean").write_text("def left := 1\n", encoding="utf-8")
        (nested / "Right.lean").write_text("def right := 2\n", encoding="utf-8")
        errors = []
        check_physical_layout(root, errors)
        assert errors == [
            "physical source directory has no direct Lean files and exactly "
            "one child directory: Outer -> Outer/Inner"
        ], errors
        assert physical_layout_metrics(root)[
            "one_child_zero_direct_lean_directories"
        ] == 1

    with tempfile.TemporaryDirectory() as temporary_name:
        root = Path(temporary_name)
        docs = root / "Docs"
        docs.mkdir()
        (docs / "README.md").write_text("supporting notes\n", encoding="utf-8")
        pair = root / "Pair"
        pair.mkdir()
        (pair / "Left.lean").write_text("def left := 1\n", encoding="utf-8")
        (pair / "Right.lean").write_text("def right := 2\n", encoding="utf-8")
        errors = []
        check_physical_layout(root, errors)
        assert not errors, errors
        assert physical_layout_metrics(root) == {
            "physical_directories": 2,
            "nested_lake_directories": 0,
            "empty_directories": 0,
            "nonempty_zero_lean_directories": 1,
            "one_child_zero_direct_lean_directories": 0,
        }

    with tempfile.TemporaryDirectory() as temporary_name:
        root = Path(temporary_name)
        for cache in (".lake", "__pycache__", ".pytest_cache"):
            (root / cache / "Empty").mkdir(parents=True)
        errors = []
        check_physical_layout(root, errors)
        assert errors == [
            "source-local Lake directory must use the workspace artifact "
            "tree: .lake"
        ], errors
        assert physical_layout_metrics(root)["physical_directories"] == 0
        assert physical_layout_metrics(root)["nested_lake_directories"] == 1

    inventory = {
        "schema_version": 1,
        "module_count": 1,
        "modules_sha256": "0" * 64,
        "modules": ["Example.lean"],
    }
    metrics: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": inventory,
        "counts": {"letI": 0},
        "internal_import_closure": {"Example": 0},
        "import_graph": {
            "internal_imports": 0,
            "external_imports": 0,
            "canonical_root_reachable_modules": 1,
            "unresolved_local_imports": 0,
            "self_imports": 0,
            "acyclic": True,
        },
        "directory_aggregation": {
            "physical_owner_directories": 0,
            "same_name_aggregates": 0,
            "direct_import_complete": 0,
            "subtree_import_complete": 0,
        },
        "files": [
            {"file": "Example.lean", "code_lines": 3, "physical_lines": 7}
        ],
    }
    baseline = architecture_baseline(metrics)
    errors: list[str] = []
    validate_baseline(baseline, metrics, errors)
    assert not errors, errors
    malformed = dict(baseline, count_ceilings={"letI": -1})
    malformed_errors: list[str] = []
    validate_baseline(malformed, metrics, malformed_errors)
    assert malformed_errors

    acyclic_graph = {"Root": ("Leaf",), "Leaf": ()}
    assert import_cycle(acyclic_graph) is None
    assert transitive_import_closure(acyclic_graph, "Root") == {"Leaf"}
    assert import_cycle({"Left": ("Right",), "Right": ("Left",)})
    assert import_cycle({"Self": ("Self",)})

    aggregate_graph = {
        "Owner": ("Owner.Left",),
        "Owner.Left": ("Owner.Right",),
        "Owner.Right": (),
    }
    assert immediate_child_modules("Owner", set(aggregate_graph)) == {
        "Owner.Left",
        "Owner.Right",
    }
    missing_direct, missing_descendants = aggregate_contract_gaps(
        "Owner", aggregate_graph
    )
    assert missing_direct == {"Owner.Right"}
    assert not missing_descendants
    complete_aggregate_graph = dict(
        aggregate_graph,
        Owner=("Owner.Left", "Owner.Right"),
    )
    assert aggregate_contract_gaps(
        "Owner", complete_aggregate_graph
    ) == (set(), set())

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--print-metrics", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--write-baseline", action="store_true")
    parser.add_argument("--skip-baseline", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(
                f"architecture-contract self-test: FAILED: {error}",
                file=sys.stderr,
            )
            return 1
        print("architecture-contract self-test: OK")
        return 0
    if args.skip_baseline and args.write_baseline:
        parser.error("--skip-baseline and --write-baseline are mutually exclusive")

    files = contract_source_files()
    graph = internal_import_graph(files)
    metrics = compute_metrics(files)
    errors: list[str] = []
    check_layout(files, graph, errors)
    if not args.skip_baseline and not args.write_baseline:
        try:
            baseline = json.loads(args.baseline.read_text(encoding="utf-8"))
        except FileNotFoundError:
            errors.append(
                f"architecture baseline is missing: {args.baseline}; "
                "run with --write-baseline after review"
            )
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"cannot read architecture baseline: {error}")
        else:
            validate_baseline(baseline, metrics, errors)

    if args.print_metrics:
        print(json.dumps(metrics, ensure_ascii=False, indent=2))
    for error in errors:
        print(f"architecture-contract: {error}", file=sys.stderr)
    if errors:
        print(
            f"architecture-contract: FAILED ({len(errors)} diagnostics)",
            file=sys.stderr,
        )
        return 1
    if args.write_baseline:
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.baseline.with_suffix(args.baseline.suffix + ".tmp")
        temporary.write_text(
            json.dumps(
                architecture_baseline(metrics),
                ensure_ascii=False,
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        temporary.replace(args.baseline)
        print(f"architecture-contract: wrote baseline {args.baseline}")
    print(
        "architecture-contract: OK "
        f"({metrics['lean_files']} modules, {metrics['code_lines']} code lines)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
