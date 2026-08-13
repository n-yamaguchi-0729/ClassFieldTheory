# Class field theory

[![Lean](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/ClassFieldTheory/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](../../LICENSE)

This directory is the production source root of the unified `ClassFieldTheory`
Lean library. Its reader-facing import is:

```lean
import ClassFieldTheory
```

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
`example` directives. Public documentation and architecture are checked
directly by the source-independent validation suite.

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
`LocalClassFieldTheory.Concrete.Finite.LocalReciprocity`, finite local
existence by `LocalClassFieldTheory.Concrete.Finite.Existence`, and local
Kummer theory by `LocalClassFieldTheory.Concrete.Kummer`.

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
- the exact kernel of the local Hilbert-symbol character and the induced
  injection from the corresponding norm quotient;
- the maximal finite Kummer pairing, packaged as a multiplicative character
  in its radical variable;
- full ray moduli with a finite part and a selected set of real places;
- ray and Hilbert class fields inside a fixed separable closure, including
  literal monotonicity of the selected subfields;
- narrow finite conductors on conductorial subgroups, the exact criterion for
  removing one real place from a defining modulus, local conductor comparison,
  finite ramification support, and conductor lattice laws;
- ideal Artin maps, decomposition laws, unramified splitting, and the principal
  ideal theorem;
- the cyclic Hasse norm theorem;
- Hasse--Arf and local/global Kronecker--Weber.

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

## Deliberate extension frontier

The finite number-field theory above is implemented. The principal mathematical
extensions that are not yet claimed are:

- maximal-abelian infinite global reciprocity beyond the existing surjective
  idèle-class Artin homomorphisms: the maximal-abelian object, the kernel
  theorem, and the infinite correspondence;
- finite-place global/local Hilbert-character comparison, finite support, and
  the all-place global product formula;
- general power-residue reciprocity derived from the Hilbert-symbol package;
- the norm limitation theorem for arbitrary finite extensions;
- the minimal full conductor whose infinite part records real-to-complex
  ramification, beyond the implemented one-real-place removal criterion;
- a full comparison equivalence between the project `ZHat` ring model and the
  general profinite additive completion.

These are tracked with dependency order and acceptance criteria in
[`CURRENT_STATUS.md`](CURRENT_STATUS.md). A declaration occurring in an
intermediate construction is not presented here as completion of one of these
larger endpoints.

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

Bare `lake build` builds the production library, which is the repository's
default target. The canonical build uses ordinary Lake output, and warnings
are fixed at their cause rather than hidden.

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

[`CURRENT_STATUS.md`](CURRENT_STATUS.md) is the only live authority for exact
green counts, active validation, build evidence, known performance debt, and
the ordered extension roadmap. This README intentionally contains no dated
green snapshot.

## License

ClassFieldTheory is distributed under the Apache License 2.0. See
[`LICENSE`](../../LICENSE).
