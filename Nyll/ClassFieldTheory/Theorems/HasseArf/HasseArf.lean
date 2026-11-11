/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import Nyll.ClassFieldTheory.Definitions.HasseArf.IsLowerRamificationJump
public import Nyll.ClassFieldTheory.HasseArf
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension

/-!
# Hasse--Arf theorem

Let `L/K` be a finite abelian extension of nonarchimedean local fields, with
the valuation of `L` extending that of `K`.  If `n` is a jump in the lower
ramification filtration, the corresponding upper index is the Herbrand
value `φ(n)`.  Hasse--Arf says that this upper index is an integer.

This is the standard equivalent integral-lower-jump formulation of the
theorem.  It avoids postulating an opaque predicate for upper jumps: the
lower groups and the Herbrand value are defined explicitly in
`ClassFieldTheory.Definitions.HasseArf` modules from Mathlib's valuation-subring
data.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

/-- **Hasse--Arf.** For a finite abelian extension of nonarchimedean local
fields, the Herbrand image of every lower ramification jump is integral.

Here the lower filtration is attached to the canonical valuation subring of
`L`.  The `Valuation.HasExtension` assumption records compatibility of the
canonical valuations on `K` and `L`; it is data about the extension, not a
ramification or integrality conclusion. -/
theorem hasseArf
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {n : ℕ}
    (hn : IsLowerRamificationJump K
      (ValuativeRel.valuation L).valuationSubring n) :
    ∃ z : ℤ,
      herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n = (z : ℚ) :=
  HasseArf.hasseArf_canonical K L hn

end ClassFieldTheory
