# Class Field Theory maintenance tools

These tools cover the production library below `Lean4/ClassFieldTheory/`.
The library includes local and global class field theory, Hasse--Arf,
Kronecker--Weber, and their shared infrastructure.

Run the source-independent static contract:

```text
python3 scripts/ClassFieldTheory/check_public_contracts.py
```

The static contracts are platform-independent. Maintenance runners that invoke
Lake or inspect active processes (`build_targets.py`,
`build_nongreen_frontier.py`, `lean_prefix_check.py`, and
`measure_performance.py`) require Linux or WSL; they use POSIX process groups,
`/proc`, file locking, or GNU `/usr/bin/time`.

The documentation contract requires a module docstring in every production
module. It scans Lean comments, Markdown, and maintained tooling metadata for
external provenance labels, source-specific wording, section citations, and
numbered-result citations.  This keeps documentation focused on the
mathematical content while excluding matches that occur only in Lean
identifiers, code, or string literals.

The companion public-API scan requires docstrings on every exported value or
type constructor (`def`, `abbrev`, `structure`, `class`, and `inductive`).
Supporting theorem names are intentionally not bulk-filled with generated
prose. Public clients import semantic owner aggregates directly; the
production tree does not maintain a parallel import-only API hierarchy.

The architecture part treats `ClassFieldTheory.lean` as the complete library
entrypoint. Its internal import closure must equal the exact production
inventory; unresolved local imports, self-imports, and cycles are
rejected, and the import-cycle count must be zero. Direct external imports are
restricted to `Mathlib`; imports from every other project source tree are
rejected.

All ClassFieldTheory artifacts and diagnostic logs use the repository-level
`.lake` tree. The artifact directory configured by `lakefile.toml` is the
single source of truth; source-local `.lake` directories are rejected so
targeted builds can reuse the same dependency artifacts.

Run targeted builds through the locked multi-target runner.  Independent
targets belong in one invocation so Lake plans their shared dependencies only
once and writes the configured central build directory from one process:

```text
python3 -B scripts/ClassFieldTheory/build_targets.py \
  AlgebraicNumberTheory.Idele.PositiveArchimedeanSection \
  GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity
```

The runner holds the workspace build lock, refuses to overlap an unmanaged
Lake or Lean writer, fixes `LEAN_NUM_THREADS=1`, and records one central log.
Use `--wait` only when a caller should wait for an already managed build.
Do not launch separate Lake processes for targets that can be supplied to the
same runner invocation.

Directory aggregation is also checked without transitive substitutes.  Every
production owner directory must have its same-named aggregate, and that
aggregate must directly import every immediate child module and every
immediate child aggregate.  Complete descendant reachability is checked in
addition to this direct-import requirement.

The checker also walks the physical source tree independently of the Lean
import graph.  It ignores `.lake`, `__pycache__`, and hidden cache directories;
rejects empty directories and directories with exactly one direct `.lean`
file; and rejects a directory with no direct Lean file and exactly one direct
child directory.  Nonempty documentation- or asset-only directories are
allowed and recorded in the physical-layout metrics.

## Choice audit

Refresh scanner-owned fields while preserving the reviewed classifications:

```text
python3 scripts/ClassFieldTheory/check_choice_contract.py --initialize-manifest
python3 scripts/ClassFieldTheory/check_choice_contract.py --refresh-manifest
python3 scripts/ClassFieldTheory/check_choice_contract.py
python3 scripts/ClassFieldTheory/render_choice_audit.py
python3 scripts/ClassFieldTheory/render_choice_audit.py --check
```

The formal initializer restores the reviewed current matrix only when the
complete direct object partition and the expected direct/derived totals match.
It refuses a newly discovered or stale object instead of assigning a default
classification.  `--refresh-manifest` updates scanner-owned source metadata
while preserving the reviewed fields; the ordinary checker and renderer
`--check` are both part of `check_public_contracts.py`.

## Architecture metrics

Before building an unfinished frontier, audit its blocking imports and source
shape without invoking Lean:

```text
python3 scripts/ClassFieldTheory/audit_nongreen.py --limit 20
python3 scripts/ClassFieldTheory/audit_nongreen.py --json > /tmp/cft-nongreen-audit.json
python3 scripts/ClassFieldTheory/audit_declaration_towers.py --limit 25
python3 scripts/ClassFieldTheory/check_performance_contract.py --static-only
```

The report ranks downstream impact, declaration span, repeated local-instance
setup, broad simplification, and direct non-green blockers.  In particular, a
module is safe to build as an isolated frontier only when its
`blocking_import_count` is zero.

The declaration-tower audit separately detects exported declaration types that
embed `letI`/finite-dimensional/scalar-tower construction and reports when the
same tower is then rebuilt in the proof body.  This is the main static warning
sign for expensive `whnf`/`isDefEq` failures in dependent field towers.  It
also counts local-instance towers moved into `structure`, `class`, or
`inductive` constructor payloads: a small container head does not make its
dependent constructor type cheap to finalize.  Giant declaration spans and
broad `simp` use are tracked separately.  The reviewed static performance
contract covers all production modules and rejects increases above the
recorded ceilings while allowing genuine reductions.  It is source-only and
does not invoke Lean or Lake.

Run the current no-green frontier safely with:

```text
python3 scripts/ClassFieldTheory/build_nongreen_frontier.py
python3 scripts/ClassFieldTheory/build_nongreen_frontier.py --max-modules 10
python3 scripts/ClassFieldTheory/build_nongreen_frontier.py --execute --max-modules 10
```

The default is a read-only dry run. It first gives all production `olean`
facets to one ordinary `lake --no-build build` planner invocation.  This permits
Lake to validate its own saved input hashes while prohibiting every build
action; no Lean process is started.  The reported trace-stale roots and their
reverse-import closure are the no-green set.  Artifact mtimes are not used as a
proxy: a dependency artifact may be newer while retaining exactly the content
hash recorded by a consumer trace.

Execution snapshots only that trace-validated frontier, orders it by physical
source length, and starts one ordinary
`LEAN_NUM_THREADS=1 lake build +<Module>:olean` process per module.
`LEAN_NUM_THREADS=1` is applied only to execution builds: it limits Lake's Lean
runtime job pool to one worker so that stale sibling dependencies cannot launch
multiple memory-heavy Lean children concurrently.  The Lake 5.0 CLI bundled
with Lean 4.32.1 has no `-j`/`--jobs` build option; the runtime environment
variable is the supported limit.  The read-only
`lake --no-build` planner is unchanged.  The runner never deliberately rebuilds
a green target, uses an exclusive lock, writes a separate timed log for each
attempt, refreshes the trace-based green count after success, and stops at the
first failure or changed-frontier condition.

After structural diagnostics pass and a metric/module-set change has been
reviewed, write the exact non-regression baseline with:

```text
python3 scripts/ClassFieldTheory/check_architecture_contract.py --write-baseline
python3 scripts/ClassFieldTheory/check_architecture_contract.py
```

The old baseline is not reusable after the source-root and ownership changes.
Write a new one only after the reorganized source tree is stable and the
architecture diagnostics have been reviewed.

Every Lean source is also capped at 3000 physical lines, so theorem-specific
files must be split along mathematical boundaries instead of hidden behind a
large generated facade. Module-size metrics separately use nonblank code lines
after removing nested Lean comments.
The schema-2 reviewed baseline records exact source ownership, import-graph and
directory-aggregation facts, plus per-file, syntax-count, and
public-import-closure ceilings.  It deliberately does not encode the former
LCFT-only directory split.  Graph and aggregation gates run even with
`--skip-baseline`; that option skips only comparison with the reviewed metric
snapshot.

## Performance baseline

With the Lean sources stable, perform the official complete measurement:

```text
python3 scripts/ClassFieldTheory/measure_performance.py --full-baseline
python3 scripts/ClassFieldTheory/check_performance_contract.py
```

The source-only declaration-risk contract is maintained separately in
`docs/declaration-performance-contract.json`; it is checked even when a full
machine-specific performance record exists.  Its deterministic scanner and
schema tests can be run with:

```text
python3 scripts/ClassFieldTheory/audit_declaration_towers.py --self-test
python3 scripts/ClassFieldTheory/check_performance_contract.py --self-test
```

The old performance record is likewise intentionally absent.  Generate it
only after a complete `ClassFieldTheory` build succeeds.

The complete refresh measures every configured incremental root, every
reviewed clean root, and the twenty code-largest modules.  Clean measurements
use disposable source/build trees and never delete or move the workspace
`.lake` directory.  Timings and memory are advisory facts, while completeness,
successful elaboration, the exact root/module sets, and source-code freshness
are enforced.  Source freshness ignores comments and blank lines.
