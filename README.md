# Class field theory

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

The production sources live under `Lean4/ClassFieldTheory`.  The canonical
entrypoint is `Lean4/ClassFieldTheory.lean`, so the reader-facing import is:

```lean
import ClassFieldTheory
```

## Main-theorem guide

`import ClassFieldTheory` exposes everything below.  For a smaller dependency
closure, use the focused import in the middle column.  Every declaration in
this table is an active production declaration; planned APIs are deliberately
not listed.

| Topic | Focused import | Headline declarations |
| --- | --- | --- |
| Finite local reciprocity | `LocalClassFieldTheory.Finite.LocalReciprocity` | `LocalClassFieldTheory.localReciprocityEquiv`<br>`LocalClassFieldTheory.localArtinMap_ker` |
| Finite local existence | `LocalClassFieldTheory.Finite.Existence` | `LocalClassFieldTheory.finiteAbelianNormSubgroupOrderIso` |
| Absolute and profinite local reciprocity | `LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity` | `LocalClassFieldTheory.absoluteLocalArtinMap`<br>`LocalClassFieldTheory.profiniteLocalReciprocity` |
| Profinite-completion comparison | `LocalClassFieldTheory.Infinite.AbstractProfiniteCompletionComparison` | `LocalClassFieldTheory.topologicalProfiniteCompletion_compare_abstract` |
| Finite global reciprocity | `GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization` | `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv` |
| Maximal-abelian global reciprocity | `GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel` | `GlobalClassFieldTheory.Reciprocity.maximalAbelianGlobalArtin_surjective`<br>`GlobalClassFieldTheory.Reciprocity.maximalAbelianGlobalArtin_ker` |
| Infinite abelian class-field correspondence | `GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence` | `GlobalClassFieldTheory.GlobalClassFields.infiniteAbelianClassFieldCorrespondence` |
| Class-field existence | `GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField` | `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_ideleClassNorm_range` |
| Ray class fields and full conductors | `GlobalClassFieldTheory.GlobalClassFields.FullConductorRayClassField` | `GlobalClassFieldTheory.GlobalClassFields.nonempty_algHom_to_rayClassField_iff_fullConductor_le` |
| Finite conductor and ramification | `GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness` | `GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus`<br>`GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces` |
| Norm limitation | `GlobalClassFieldTheory.GlobalClassFields.NormLimitation` | `GlobalClassFieldTheory.GlobalClassFields.normLimitation` |
| Cyclic Hasse norm theorem | `GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple` | `GlobalClassFieldTheory.ClassFieldAxiom.hasseNormPrinciple_cyclic` |
| Hilbert class field and principal ideal theorem | `GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalization` | `GlobalClassFieldTheory.IdealClassFieldTheory.allIdealsBecomePrincipalInSmallHilbertClassField` |
| Local Kummer and Hilbert pairing | `LocalClassFieldTheory.Kummer` | `LocalClassFieldTheory.Kummer.localHilbertPairing_nondegenerate`<br>`LocalClassFieldTheory.Kummer.localHilbertSymbol_tame_formula` |
| Global Hilbert product formula | `GlobalClassFieldTheory.Reciprocity.HilbertProductFormula` | `GlobalClassFieldTheory.Reciprocity.globalHilbertProduct_principal`<br>`GlobalClassFieldTheory.Reciprocity.hilbertSymbol_allPlaces_product_eq_one` |
| Power-residue reciprocity with bad-place correction | `GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity` | `GlobalClassFieldTheory.Reciprocity.powerResidueBadFinitePlaces`<br>`GlobalClassFieldTheory.Reciprocity.idealPowerResidueSymbol_reciprocity_with_bad_place_correction` |
| Gauss quadratic reciprocity from global CFT | `GlobalClassFieldTheory.Reciprocity.RationalQuadraticPowerResidueReciprocity` | `GlobalClassFieldTheory.Reciprocity.gaussReciprocity_nat_from_powerResidueReciprocity`<br>`GlobalClassFieldTheory.Reciprocity.gaussReciprocity_nat_from_powerResidueReciprocity_eq_mathlib` |
| Hasse--Arf | `HasseArf` | `HasseArf.isLocalUpperRamificationJump_int` |
| Local and global Kronecker--Weber | `KroneckerWeber` | `KroneckerWeber.exists_localCyclotomicEmbedding`<br>`KroneckerWeber.exists_cyclotomicEmbedding` |

The root is a complete import closure, not a sample or a hand-maintained list of
headline files. The architecture contract checks that every production module
is reachable from `ClassFieldTheory`, that local imports resolve, and that the
import graph has no cycles. Every production owner directory has a
same-named aggregate that directly imports each immediate child module and
child aggregate. Empty directories and directories with no direct Lean file
and exactly one child directory are rejected.

The only permitted external Lean dependency is Mathlib. Imports between
modules owned by this library are internal; imports from `Progress`, `Legacy`,
or any other project source tree are rejected by the architecture contract.

Production modules contain no `#check`, `#print`, `#lint`, `#synth`, or
`example` directives.  The validation suite checks the published production
root directly.

## Public entrypoints

- `ClassFieldTheory`: the complete library.
- `LocalClassFieldTheory`: finite and profinite local reciprocity.
- `GlobalClassFieldTheory.MainStatements`: the compact public surface for
  number-field global class field theory.
- `HasseArf`: integrality of upper ramification jumps.
- `KroneckerWeber`: the local and global Kronecker--Weber theorems.

For the main global statements, use:

```lean
import GlobalClassFieldTheory.MainStatements
```

Focused users should import the semantic owner aggregate directly. For
example, finite local reciprocity is owned by
`LocalClassFieldTheory.Finite.LocalReciprocity`, finite local existence by
`LocalClassFieldTheory.Finite.Existence`, and local Kummer theory by
`LocalClassFieldTheory.Kummer`.

## Implemented scope

The library connects the following layers with concrete Lean constructions:

- abstract class formations, degree, norm, Frobenius, transfer, and finite
  reciprocity;
- valuation theory, local fields, ramification, cohomology, Kummer theory, and
  Lubin--Tate theory;
- finite and profinite local class field theory;
- number-field idèles and idèle classes, the class-field axiom, finite global
  reciprocity, and finite abelian class-field correspondence;
- the infinite global Artin homomorphism for arbitrary abelian Galois
  extensions, its continuous descent to the idèle class group, dense image,
  and surjectivity;
- maximal-abelian global reciprocity, with kernel equal to the idèle-class
  identity component, and the infinite abelian class-field correspondence;
- the exact kernel of the local Hilbert-symbol character and the induced
  injection from the corresponding norm quotient;
- the maximal finite Kummer pairing, packaged as a multiplicative character
  in its radical variable;
- finite-place global/local Hilbert-character comparison, finite support, and
  the all-place Hilbert product formula;
- general ideal power-residue reciprocity with an explicit product of infinite
  and exponent-prime Hilbert factors as its bad-place correction;
- Gauss quadratic reciprocity over `ℚ`, including the evaluated dyadic
  correction and an equality with Mathlib's independent theorem;
- full ray moduli with a finite part and a selected set of real places;
- ray and Hilbert class fields inside a fixed separable closure, including
  literal monotonicity of the selected subfields;
- full and narrow finite conductors on conductorial subgroups, the exact
  ray-class-field embedding criterion, the criterion for removing one real
  place from a defining modulus, local conductor comparison, finite
  ramification support, and conductor lattice laws;
- ideal Artin maps, decomposition laws, unramified splitting, and the principal
  ideal theorem;
- norm limitation for arbitrary finite number-field extensions;
- the cyclic Hasse norm theorem;
- Hasse--Arf, local/global Kronecker--Weber, and the comparison from the
  topological profinite completion to the abstract open-finite-quotient limit.

The concrete global theory currently concerns number fields. It does not claim
an implementation of global function-field class field theory.

## Installation and use

The library uses Lean 4.32.1 and Mathlib 4.32.1. Clone the repository, then run:

```bash
lake exe cache get
lake build ClassFieldTheory
```

Client files can import the complete library with `import ClassFieldTheory`,
or import a semantic owner aggregate for a smaller dependency closure.

### Hasse--Arf

```lean
import HasseArf

#check HasseArf.isLocalUpperRamificationJump_int
```

The theorem uses the actual real lower and upper ramification filtrations,
natural-ceiling filtration infrastructure, Lubin--Tate ramification
calculations, and filtered local reciprocity. It also handles the possible
endpoint `-1`. Reusable ingredients remain in their mathematical owner
directories, while `HasseArf.lean` is the thin production entrypoint for the
final theorem.

### Kronecker--Weber

```lean
import KroneckerWeber

#check KroneckerWeber.exists_cyclotomicEmbedding
```

For every number field `L` that is Abelian Galois over `ℚ`, the global theorem
produces a positive integer `n` and a `ℚ`-algebra embedding
`L →ₐ[ℚ] CyclotomicField n ℚ`. The full root also exposes:

```lean
import KroneckerWeber

#check KroneckerWeber.exists_localCyclotomicEmbedding
#check KroneckerWeber.exists_structuredLocalCyclotomicEmbedding
```

Reusable compositum, ramification, inertia, unramifiedness,
valuation-localization, and completion results remain in their semantic owner
libraries. The `KroneckerWeber` aggregate exposes the production cyclotomic
construction and final local-to-global argument.

## Scope boundary

The number-field results listed above, including general power-residue
reciprocity and its Gauss specialization, are active production results. The
library does not claim global function-field class field theory.

## Ownership and public design

Shared algebraic-number-theory, valuation, local-field, ramification,
cohomology, Kummer, and Lubin--Tate declarations live in their mathematical
owner directories. Same-named files aggregate directory contents; redundant
import-only compatibility facades are not part of the public design.

The most expensive elaboration failures in this tree have generally come from
large import closures together with repeated, propositionally equal but
non-definitionally-equal `Algebra`, `FiniteDimensional`, `IsScalarTower`,
quotient, or fixed-field instance paths. File length and broad `simp` use are
audit signals, but neither is a sufficient diagnosis by itself.

The durable boundary is therefore:

- one canonical instance path in the provider;
- an explicitly typed or opaque bridge at the module boundary;
- a small consumer API, such as a named character or its actual Galois value;
- one shared middle datum when several results use the same dependent
  endpoints.

Consumers should not reconstruct raw factored maps or fixed-field witnesses
with independently inferred instances.

## Build and verification

From the repository root, build the production library with:

```bash
lake build ClassFieldTheory
```

The repository's default target is `ClassFieldTheory`.  The canonical build
uses ordinary Lake output; warnings are fixed at their cause rather than
hidden.

The validation suite is:

```bash
python3 -B scripts/ClassFieldTheory/check_public_contracts.py

python3 -B scripts/ClassFieldTheory/green_status.py \
  --probe-timeout 240 --json --list-no-green --list-frontier
```

The public-contract suite includes documentation, public API, architecture,
choice-boundary, and performance checks. Source-level `set_option`, `sorry`,
`admit`, new `axiom` declarations, `nolint`, and warning suppression are not
accepted as repairs.

This README intentionally contains no dated green snapshot.

## License

ClassFieldTheory is distributed under the Apache License 2.0. See
[`LICENSE`](LICENSE).
