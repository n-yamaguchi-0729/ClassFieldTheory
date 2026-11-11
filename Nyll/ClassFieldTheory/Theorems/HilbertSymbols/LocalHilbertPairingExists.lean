/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Mathlib.NumberTheory.LocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Small

/-!
# Existence of the local Hilbert pairing

Let `K` be a nonarchimedean local field containing the `n`-th roots of
unity, with `n` nonzero in `K`.  The local Hilbert symbol descends to a
bimultiplicative pairing

`Kˣ / (Kˣ)^n × Kˣ / (Kˣ)^n → μₙ(K)`.

The theorem below records the pairing laws without naming a particular
implementation of local reciprocity in its statement. Its proof imports the
implementation layer. The witness satisfies the
Steinberg relation, skew-symmetry, nondegeneracy in both variables, and the
Kummer norm-residue vanishing criterion.  Multiplicativity is already part
of the type `HilbertPairing K n`.
The witness is the named pairing built from the specified general local Artin map;
its value normalization is recorded in `LocalHilbertPairingArtinNormalization`.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- A nonarchimedean local field containing the `n`-th roots of unity admits
a nondegenerate, skew-symmetric Hilbert pairing satisfying the Steinberg and
Kummer norm-residue laws. -/
theorem exists_localHilbertPairing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ B : HilbertPairing K n,
      HilbertPairing.IsLocalHilbertPairing B :=
  ⟨localHilbertPairing K n hnK hmu,
    localHilbertPairing_isLocalHilbertPairing K n hnK hmu⟩

end ClassFieldTheory
