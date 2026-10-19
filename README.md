# ClassFieldTheory (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Developed as part of [NYLL](https://github.com/n-yamaguchi-0729/NYLL), this Lean library treats class field theory for
nonarchimedean local fields, number fields and function fields over finite fields.
The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/class-field-theory/) presents reciprocity, existence and the other selected results
with their mathematical hypotheses and links to the formal proofs.

## Main results

<!-- nyll-publication:cft-main-results:begin -->
### Local class field theory

Let K be a nonarchimedean local field.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity.lean#L33) | For each finite abelian extension L/K, a continuous surjective Artin map Kˣ → Gal(L/K) has kernel N(Lˣ). |
| [Existence and classification](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean#L33) | Finite abelian extensions in a fixed separable closure correspond, with reversed inclusion, to open finite-index subgroups of Kˣ via norms. |

### Global class field theory: number fields

Let K be a number field.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean#L31) | Each finite abelian extension L/K admits a modulus and a surjective ray-class Artin map to Gal(L/K), sending prime classes away from the modulus to arithmetic Frobenius. |
| [Class-field existence](Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupExistence.lean#L27) | Every subgroup of a ray class group is the kernel of the Frobenius-normalized Artin map of a finite abelian extension. |

### Global class field theory: function fields

Let K be a function field in one variable over a finite field k.

| Result | Mathematical content |
| --- | --- |
| [Finite abelian reciprocity](Nyll/ClassFieldTheory/Theorems/FunctionField/FiniteReciprocity.lean#L66) | For each finite abelian extension L/K, the Artin map identifies C_K / N(C_L) with Gal(L/K), where C denotes the idèle class group. |
| [Class-field existence and uniqueness](Nyll/ClassFieldTheory/Theorems/FunctionField/ClassField.lean#L60) | Every open finite-index subgroup of C_K in its usual topology is the norm subgroup of a unique finite abelian extension in a fixed separable closure. |
<!-- nyll-publication:cft-main-results:end -->

## Public API

Use [leanprover/lean4:v4.35.0-rc2](lean-toolchain) and the Mathlib revision pinned in
[lake-manifest.json](lake-manifest.json). Add this dependency to your project’s
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/ClassFieldTheory.git"
rev = "main"
```

Run `lake update Nyll`, then commit your generated lake-manifest.json to retain
the resolved revisions. Import the library in a Lean file:

```lean
import Nyll.ClassFieldTheory.All
```

The standalone distributions share the package name Nyll. Choose one distribution;
for several libraries together, use [NYLL](https://github.com/n-yamaguchi-0729/NYLL).

To build a checkout of this repository, run from its root:

```sh
lake exe cache get
lake --wfail build
```

## Verification

[CI](.github/workflows/lean.yml) checks the import closure, builds with
warnings as errors, audits declarations, and verifies proofs with NanoDa
and the Lean kernel. The [public API contract](.github/verification/main-declarations.json)
checks the named declarations and their source modules.

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
