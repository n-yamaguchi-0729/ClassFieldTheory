# Verification

The [Lean workflow](../workflows/lean.yml) uses a repository-specific verification policy. Run it from the repository root. Its two
repository-specific inputs are:

- `manifest-config.json`: maintained source owners, import roots, and exact
  Lean and mathlib pins.
- `main-declarations.json`: selected public declarations whose names, kinds,
  owner, and specified source modules must remain available.

The other files implement the shared procedure:

1. `generate_manifest.py` inventories every maintained physical Lean source,
   checks its import reachability and source policy, and records source hashes.
2. `setup_tools.py` obtains and builds pinned `lean4export` and NanoDa revisions.
   The workflow obtains the pinned Lean toolchain and mathlib cache first.
3. `verify.py` runs the mandatory build with warnings as errors, inventories
   every declaration (including private declarations), selects and exports the
   safe declaration union, checks exact export coverage, checks it with NanoDa,
   without a separate fresh-environment official kernel replay. `Inventory.lean`
   and `ExportSelected.lean` implement the active Lean audit/export stages.
   The optional replay implementation is retained but is not scheduled by CI.
4. `check_main_declarations.py` checks the selected public API against the
   audited inventory and the successful verification receipts. This checks
   declaration presence and kind; it does not compare theorem statements.
5. The workflow checks whitespace and uploads logs, manifests, and receipts
   even if a stage fails.

The runtime stages run in order: build, inventory, selection, export, coverage,
and NanoDa. Every active stage must pass. The explicit proof-only aggregate
gate checks the same run, commit, physical source/configuration hashes, checker
pins, exact stage set, receipts, and artifacts before declaring success.
Its final receipt explicitly records official kernel replay as not run. Use a fresh output directory
for each local attempt and follow the commands in the workflow; a static source
audit alone does not verify proofs. The workflow keeps its artifacts for 14 days.

## Incremental build stages

CI builds local modules library by library, subdividing ClassFieldTheory into
natural sublibraries, and saves completed project
compiler outputs after each stage. The cache excludes downloaded dependencies,
toolchains, and large generated `*.setup.json` inputs. It checks the available
archive space before saving and validates cached file hashes on restoration;
a missing or invalid cache falls back to a normal build. A separate verification
job still runs the complete declaration and NanoDa checks on every
run, including cache hits. Build stages stop after five hours to leave time for
saving completed outputs and diagnostic receipts before the runner deadline.

## Live diagnostics

The verifier prints flushed START/END messages and a heartbeat every 60 seconds
for the active stage. Detailed checker output and the unchanged success receipts
remain in the verification artifact. If a runner is shut down before artifact
upload, the Actions job log still identifies the last stage reached and its
elapsed time. A heartbeat is progress information, never proof of success.
