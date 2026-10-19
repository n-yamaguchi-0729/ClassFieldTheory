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

## Main results

<!-- nyll-publication:cft-main-results:begin -->
### Local class field theory

Let K be a nonarchimedean local field.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity.lean#L33) | For each finite abelian extension L/K, a continuous surjective Artin map Kˣ → Gal(L/K) has kernel N(Lˣ). |
| [Existence and classification](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean#L33) | Finite abelian extensions in a fixed separable closure correspond, with reversed inclusion, to open finite-index subgroups of Kˣ via norms. |
| [Profinite reciprocity](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/ProfiniteLocalReciprocity.lean#L28) | The topological profinite completion of Kˣ is isomorphic to the abelianized absolute Galois group. |

### Global class field theory: number fields

Let K be a number field.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean#L31) | Each finite abelian extension L/K admits a modulus and a surjective ray-class Artin map to Gal(L/K), sending prime classes away from the modulus to arithmetic Frobenius. |
| [Class-field existence](Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupExistence.lean#L27) | Every subgroup of a ray class group is the kernel of the Frobenius-normalized Artin map of a finite abelian extension. |
| [Topological reciprocity](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/TopologicalGlobalReciprocity.lean#L31) | The idèle class group modulo its identity component is isomorphic as a topological group to the abelianized absolute Galois group. |

### Global class field theory: function fields

Let K be a function field in one variable over a finite field k.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/FunctionField/FiniteReciprocity.lean#L66) | For each finite abelian extension L/K, the Artin map identifies C_K / N(C_L) with Gal(L/K), where C denotes the idèle class group. |
| [Class-field existence and uniqueness](Nyll/ClassFieldTheory/Theorems/FunctionField/ClassField.lean#L60) | Every open finite-index subgroup of C_K in its usual topology is the norm subgroup of a unique finite abelian extension in a fixed separable closure. |
| [Profinite reciprocity](Nyll/ClassFieldTheory/Definitions/FunctionField/ProfiniteReciprocity.lean#L59) | The topological profinite completion of C_K is isomorphic to the abelianized absolute Galois group. |
<!-- nyll-publication:cft-main-results:end -->

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
