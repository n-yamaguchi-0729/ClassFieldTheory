# ClassFieldTheory

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library for local and global class field theory over number fields.
The required valuation theory, Galois cohomology, and profinite-group modules
are included, so the repository depends only on Mathlib.

## Scope

The library includes:

- abstract class formations and reciprocity;
- local reciprocity and the local existence theorem;
- global Artin reciprocity, ray class fields, and Hilbert class fields;
- conductor theory, norm limitation, and the principal ideal theorem;
- Hasse--Arf and the local and global Kronecker--Weber theorems;
- Hilbert symbols, power-residue reciprocity, and quadratic reciprocity.

Global function-field class field theory is not included.

## Build

The repository pins Lean 4.34.0 and its Mathlib revision. From the repository
root, run:

```console
lake exe cache get
lake --wfail build
```

## Use

Import the complete library with:

```lean
import ClassFieldTheory.All
```

Focused modules and folder aggregates can be imported to reduce the dependency
closure, for example:

```lean
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.All
```

API documentation is available at the
[Yamaguchi Lean 4 Library](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/).

## Verification

GitHub Actions builds the pinned source with warnings treated as errors, checks
the source and declaration inventories, runs NanoDa, and replays the result with
the Lean kernel.

## License

Apache License 2.0. See [LICENSE](LICENSE).
