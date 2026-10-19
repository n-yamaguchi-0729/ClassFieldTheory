# ClassFieldTheory (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Developed as part of [NYLL](https://github.com/n-yamaguchi-0729/NYLL), this Lean library treats class field theory for
nonarchimedean local fields, number fields and function fields over finite fields.
The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/class-field-theory/) presents reciprocity, existence and the other selected results
with their mathematical hypotheses and links to the formal proofs.

## Scope

<!-- nyll-publication:cft-scope:begin -->
Local class field theory covers nonarchimedean local fields. Global class field
theory covers number fields and function fields over finite fields, including
reciprocity, existence, norm subgroups, conductors and ray class fields.
<!-- nyll-publication:cft-scope:end -->

## Included sources

<!-- nyll-publication:distribution:begin -->
Only the module-level import closure of `Nyll.ClassFieldTheory.All` is bundled. Dependencies retain their canonical `Nyll` imports.

Supporting modules are included from [AlgebraicCurves](Nyll/AlgebraicCurves/), [GaloisCohomology](Nyll/GaloisCohomology/), [ProCGroups](Nyll/ProCGroups/), [SchemeTheory](Nyll/SchemeTheory/), [ValuedFieldTheory](Nyll/ValuedFieldTheory/). These dependency libraries are included only to the extent required by the imports.
<!-- nyll-publication:distribution:end -->

## Public API

<!-- nyll-publication:cft-public-api:begin -->
Import the complete library for local fields, number fields and function fields:

```lean
import Nyll.ClassFieldTheory.All
```

For a smaller dependency set, import an individual result directly, for example:

```lean
import Nyll.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocity
```

The [Definitions](Nyll/ClassFieldTheory/Definitions/All.lean) and [Theorems](Nyll/ClassFieldTheory/Theorems/All.lean) facades provide the vocabulary and statements collected in those sublibraries; the full entry point above includes every maintained part of the development.
<!-- nyll-publication:cft-public-api:end -->

## Build

The repository pins the Lean toolchain and dependencies.

```console
lake exe cache get
lake --wfail build
```

Elaboration and linter options are shared in `lakefile.toml`:
`autoImplicit = false`, unused-variable and missing-documentation checks,
and the standard linter set. Maintained sources do not override these options.

## Verification

The [GitHub Actions workflow](.github/workflows/lean.yml) checks that every
maintained source is reachable from `Nyll`, builds with warnings
as errors, audits all declarations for proof placeholders and unexpected axioms,
checks proofs with NanoDa, and replays them with the Lean kernel. It also checks
that the designated declarations in the [public API contract](.github/verification/main-declarations.json)
retain their names, kinds, and specified source modules. This API check does not compare
theorem statements. Logs and receipts are uploaded as workflow artifacts.

CI builds local modules in dependency-depth stages and saves completed project
compiler outputs after each stage. The cache excludes downloaded dependencies,
toolchains, and large generated `*.setup.json` inputs. It checks the available
archive space before saving and validates cached file hashes on restoration;
a missing or invalid cache falls back to a normal build. A separate verification
job still runs the complete declaration, NanoDa, and Lean kernel checks on every
run, including cache hits. Build stages stop after five hours to leave time for
saving completed outputs and diagnostic receipts before the runner deadline.

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.

## License

<!-- nyll-publication:credits:begin -->
Apache License 2.0. See [LICENSE](LICENSE).

Included adaptations from [pi1](https://github.com/chrisflav/pi1) and [Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem) retain their source-specific copyrights and authors.
The included-file inventories and preserved upstream notices are in [NOTICE](NOTICE).
<!-- nyll-publication:credits:end -->
