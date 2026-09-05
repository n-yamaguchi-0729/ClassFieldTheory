# ClassFieldTheory

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 formalization of local class field theory and global class field theory
for **number fields**. Required valuation and Galois cohomology support modules
are bundled. Documentation and the library catalog:
[Yamaguchi Lean 4 Library](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/).

## Main results

- Local reciprocity and the local existence theorem, including profinite local reciprocity.
- Global Artin reciprocity and finite and infinite abelian class-field correspondences.
- Ray and Hilbert class fields, conductor theory, norm limitation, and the principal ideal theorem.
- Hasse–Arf and local and global Kronecker–Weber.
- The Hilbert-symbol product formula, power-residue reciprocity, and Gauss quadratic reciprocity.

The global theory concerns number fields; global function-field class field theory
is outside this library's scope.

## Build and use

Use **Lean 4.33.0** and the checked-in `lake-manifest.json`, which pins Mathlib
to `6f1ef4e5dd604a435bddba4747b13970cd65d2a1`. From the repository root:

```console
lake exe cache get
lake --wfail build
```

The default build covers all maintained modules, including the bundled support
libraries. Import the whole library:

```lean
import ClassFieldTheory
```

For a smaller dependency closure, use a focused module or aggregate, such as:

```lean
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.All
```

Module paths now use the `ClassFieldTheory.` prefix and `.All` for folder
aggregates; the top-level `import ClassFieldTheory` is preserved.

## Kronecker–Weber

Every number field that is abelian Galois over the rationals embeds into a
cyclotomic field. The exact statement and its use are:

```lean
import ClassFieldTheory.KroneckerWeber.Core

example (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧ Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  KroneckerWeber.exists_cyclotomicEmbedding L
```

`IsAbelianGalois` is Mathlib's standard class for a Galois extension with
commutative automorphism group. See the
[theorem source](Lean4/ClassFieldTheory/KroneckerWeber/Core.lean).

## Verification

The [Lean workflow](.github/workflows/lean.yml) builds with warnings as errors,
checks the main theorem entries, audits declaration dependencies against
`propext`, `Classical.choice`, and `Quot.sound`, and runs NanoDa and the
official Lean kernel replay. Workflow artifacts contain the logs and receipts;
check the run's commit and result in GitHub Actions.

This library was developed with AI assistance by a non-specialist; please review the material independently.

## License

Apache License 2.0. See [LICENSE](LICENSE).
