# ClassFieldTheory (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4.35.0-rc2 library for local and global class field theory.

All original code in this library is written by OpenAI Codex.

This library is extracted from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).
Bundled dependencies use the same `Nyll` imports as the complete library.

## Scope

The local theory concerns nonarchimedean local fields, and the global theory
concerns number fields. The library covers reciprocity and existence theorems,
Hasse--Arf, Hilbert symbols, norm theorems, conductors and ray class fields,
and Frobenius and Hilbert class fields.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Finite local reciprocity](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity.lean) | A surjective continuous local Artin map `Kˣ → Gal(L/K)` whose kernel is the field-norm subgroup. |
| [Profinite local reciprocity](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/ProfiniteLocalReciprocity.lean) | The topological profinite completion of `Kˣ` is continuously multiplicatively equivalent to the abelianized absolute Galois group of a nonarchimedean local field. |
| [Local existence theorem](Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean) | The contravariant correspondence between finite abelian local extensions and open finite-index norm subgroups. |
| [Finite global reciprocity](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean) | A Frobenius-normalized surjective Artin map from a ray class group for every finite abelian extension. |
| [Topological global reciprocity](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/TopologicalGlobalReciprocity.lean) | The idèle-class quotient by its identity component is topologically isomorphic to the abelianized absolute Galois group. |
| [Global Artin map](Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/MaximalAbelianGlobalArtin.lean) | A continuous surjective global Artin map with the identity component as kernel. |
| [Hasse--Arf theorem](Nyll/ClassFieldTheory/Theorems/HasseArf/HasseArf.lean) | For a finite abelian local extension, the Herbrand value of every lower ramification jump is integral. |
| [Perfect local Hilbert pairing](Nyll/ClassFieldTheory/Theorems/HilbertSymbols/LocalHilbertPairingPerfectExists.lean) | Existence of a perfect local Hilbert pairing with the Kummer norm-residue criterion. |
| [Hilbert product formula](Nyll/ClassFieldTheory/Theorems/HilbertSymbols/HilbertProductFormula.lean) | A coherent family of local Hilbert pairings satisfying finite support and the global product formula. |
| [Cyclic Hasse norm theorem](Nyll/ClassFieldTheory/Theorems/NormTheorems/CyclicHasseNormTheorem.lean) | For a finite cyclic number-field extension, global norms are exactly the everywhere-local norms. |
| [Abelian conductor](Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/ExistsUniqueAbelianConductor.lean) | Unique existence of the conductor of a finite abelian extension. |
| [Ray class fields](Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassFieldReciprocity.lean) | Existence of a ray class field realization with its Artin reciprocity isomorphism. |
| [Big Hilbert class field](Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldArtinEquiv.lean) | The narrow ideal class group as the Frobenius-normalized Galois group of a big Hilbert class field. |
| [Small Hilbert class field](Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldArtinEquiv.lean) | The ordinary ideal class group as the Galois group of a small Hilbert class field. |
| [Principal ideal theorem](Nyll/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldPrincipalization.lean) | The principal ideal theorem for the small Hilbert class field. |
| [Kronecker--Weber theorem](Nyll/ClassFieldTheory/Theorems/KroneckerWeber.lean) | Every finite abelian extension of `ℚ` embeds into a cyclotomic field of positive order. |

Further results include local Kronecker--Weber, general power-residue
reciprocity, and Gauss quadratic reciprocity.

## Incomplete results

Global function-field class field theory is not included.

## Public API

The reader-facing API is split into two layers.

- [`Nyll.ClassFieldTheory.Definitions`](Nyll/ClassFieldTheory/Definitions/All.lean)
  contains the mathematical vocabulary used in the main statements. Definition
  files are independent of implementation modules.
- [`Nyll.ClassFieldTheory.Theorems`](Nyll/ClassFieldTheory/Theorems/All.lean)
  contains stable statements of the main results. The statements use the public
  definitions; their proofs may import the implementation library.

Use only the definitions:

```lean
import Nyll.ClassFieldTheory.Definitions.All
```

Use all public statements:

```lean
import Nyll.ClassFieldTheory.Theorems.All
```

Use the complete library, including implementation modules:

```lean
import Nyll.ClassFieldTheory.All
```

Each public theorem normally has its own file and can be imported independently,
for example:

```lean
import Nyll.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocity
```

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

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.

## License

Apache License 2.0. See [LICENSE](LICENSE). Bundled scheme-theory foundations
retain the [Anthropic FLT notices](Nyll/SchemeTheory/ANTHROPIC_FLT_NOTICE).
