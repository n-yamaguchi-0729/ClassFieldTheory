# ClassFieldTheory

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library formalizing local class field theory for nonarchimedean local
fields and global class field theory for number fields.
Its only Lake dependency is Mathlib; no sibling repository checkout is required.
The exact supporting modules from valuation theory, Galois cohomology, and
profinite groups are included in this repository.
Only the modules reachable from `ClassFieldTheory.All` are included; the
supporting directories are not copies of those complete libraries.

## Public API

The reader-facing API is split into two layers.

- [`ClassFieldTheory.Definitions`](Lean4/ClassFieldTheory/Definitions/All.lean)
  contains the mathematical vocabulary used in the main statements. Primitive
  files import Mathlib only; derived files import other definition files, not
  implementation modules.
- [`ClassFieldTheory.Theorems`](Lean4/ClassFieldTheory/Theorems/All.lean)
  contains stable statements of the main results. The statements use Mathlib
  objects and the public definitions; their proofs may import the implementation
  library.

Use only the definitions:

```lean
import ClassFieldTheory.Definitions.All
```

Use all public statements:

```lean
import ClassFieldTheory.Theorems.All
```

Use the complete library, including implementation modules:

```lean
import ClassFieldTheory.All
```

Each public theorem normally has its own file and can be imported independently,
for example:

```lean
import ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocity
```

The definition topics are local class field theory, global class field theory,
Hasse--Arf, Hilbert symbols, norm theorems, conductors and ray class fields, and
Frobenius and Hilbert class fields. Each topic also has an `All.lean` aggregate.

## Main results

All declarations below are in the `ClassFieldTheory` namespace. The linked file
is also the focused import module, with `/` replaced by `.` and `.lean` removed.

| Result | Mathematical content |
| --- | --- |
| [`finiteAbelianLocalReciprocity`](Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity.lean) | A surjective continuous local Artin map `Kˣ → Gal(L/K)` whose kernel is the field-norm subgroup. |
| [`profiniteLocalReciprocity`](Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/ProfiniteLocalReciprocity.lean) | The topological profinite completion of `Kˣ` is continuously multiplicatively equivalent to the abelianized absolute Galois group of a nonarchimedean local field. |
| [`finiteAbelianLocalExistence_orderIso`](Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean) | The contravariant correspondence between finite abelian local extensions and open finite-index norm subgroups. |
| [`finiteAbelianGlobalReciprocity`](Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean) | A Frobenius-normalized surjective Artin map from a ray class group for every finite abelian extension. |
| [`topologicalGlobalReciprocity`](Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/TopologicalGlobalReciprocity.lean) | The idèle-class quotient by its identity component is topologically isomorphic to the abelianized absolute Galois group. |
| [`maximalAbelianGlobalArtin`](Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/MaximalAbelianGlobalArtin.lean) | A continuous surjective global Artin map with the identity component as kernel. |
| [`hasseArf`](Lean4/ClassFieldTheory/Theorems/HasseArf/HasseArf.lean) | For a finite abelian local extension, the Herbrand value of every lower ramification jump is integral. |
| [`exists_perfectLocalHilbertPairing`](Lean4/ClassFieldTheory/Theorems/HilbertSymbols/LocalHilbertPairingPerfectExists.lean) | Existence of a perfect local Hilbert pairing with the Kummer norm-residue criterion. |
| [`exists_globalHilbertPairingFamily_productFormula`](Lean4/ClassFieldTheory/Theorems/HilbertSymbols/HilbertProductFormula.lean) | A coherent family of local Hilbert pairings satisfying finite support and the global product formula. |
| [`cyclicHasseNormTheorem`](Lean4/ClassFieldTheory/Theorems/NormTheorems/CyclicHasseNormTheorem.lean) | For a finite cyclic number-field extension, global norms are exactly the everywhere-local norms. |
| [`existsUnique_abelianConductor`](Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/ExistsUniqueAbelianConductor.lean) | Unique existence of the conductor of a finite abelian extension. |
| [`rayClassField_reciprocity`](Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassFieldReciprocity.lean) | Existence of a ray class field realization with its Artin reciprocity isomorphism. |
| [`bigHilbertClassField_artinEquiv`](Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldArtinEquiv.lean) | The narrow ideal class group as the Frobenius-normalized Galois group of a big Hilbert class field. |
| [`smallHilbertClassField_artinEquiv`](Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldArtinEquiv.lean) | The ordinary ideal class group as the Galois group of a small Hilbert class field. |
| [`ideals_becomePrincipalInSmallHilbertClassField`](Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldPrincipalization.lean) | The principal ideal theorem for the small Hilbert class field. |
| [`kroneckerWeber`](Lean4/ClassFieldTheory/Theorems/KroneckerWeber.lean) | Every finite abelian extension of `ℚ` embeds into a cyclotomic field of positive order. |

The implementation directories include `Algebra`, `AlgebraicNumberTheory`,
`AbstractClassFieldTheory`, `LocalFieldTheory`, `LocalClassFieldTheory`,
`GlobalClassFieldTheory`, `RamificationTheory`, `HasseArf`, `KummerTheory`,
`LubinTate`, and `KroneckerWeber`. They provide the proofs behind the public
theorem layer; users who only need the headline results can import the
corresponding `Theorems` files instead. Further detailed results, including
local Kronecker--Weber, general power-residue reciprocity, and Gauss quadratic
reciprocity, currently live in these implementation modules.

Global function-field class field theory is not included.

## Build

The repository pins Lean 4.34.0 and an exact Mathlib revision.

```console
lake exe cache get
lake --wfail build
```

## Verification

The [GitHub Actions workflow](.github/workflows/lean.yml) checks that every
maintained source is reachable from `ClassFieldTheory.All`, builds with warnings
as errors, audits all declarations for proof placeholders and unexpected axioms,
checks proofs with NanoDa, and replays them with the Lean kernel. It also checks
that the designated declarations in the [public API contract](.github/verification/main-declarations.json)
retain their names, kinds, and specified source modules. This API check does not compare
theorem statements. Logs and receipts are uploaded as workflow artifacts.

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and preparation of this repository.
[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) is the human author and responsible maintainer.

## License

Apache License 2.0. See [LICENSE](LICENSE).
