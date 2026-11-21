/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.Different.Powers
public import Nyll.ValuedFieldTheory.Ramification.Different.TraceIdeal

/-!
# Exact trace images of integer powers

The actual different and ramification index determine the trace image at every
integer level, including negative levels. The floor is integer division by the
positive ramification index; no tame or Galois hypothesis is imposed.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors
open IsLocalRing FractionalIdeal

namespace RamificationTheory.DiscreteValuationRing

variable (A K B L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- Containment of a trace image is equivalent to the exact inequality between
integer depths and the exponent of the actual different. -/
theorem traceImage_maximalIdeal_zpow_le_iff (r s d : ℤ)
    (hd : (differentIdeal A B : FractionalIdeal B⁰ L) =
      (maximalIdeal B : FractionalIdeal B⁰ L) ^ d) :
    traceImage A K ((maximalIdeal B : FractionalIdeal B⁰ L) ^ r) ≤
        (maximalIdeal A : FractionalIdeal A⁰ K) ^ s ↔
      s ≤ (r + d) / ((maximalIdeal B).ramificationIdx A : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective A K) (h.trans (map_zero _).symm))
  have hπB : spanSingleton B⁰ (algebraMap K L (algebraMap A K π)) =
      (maximalIdeal B : FractionalIdeal B⁰ L) ^
        (maximalIdeal B).ramificationIdx A := by
    have h := congrArg (fun J : Ideal B => (J : FractionalIdeal B⁰ L))
      (map_maximalIdeal_eq_pow_ramificationIdx A B)
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      coeIdeal_span_singleton, coeIdeal_pow] at h
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
    exact h
  have hmB : (maximalIdeal B : FractionalIdeal B⁰ L) ≠ 0 :=
    coeIdeal_ne_zero.mpr (IsDiscreteValuationRing.not_a_field B)
  have hdual : dual A K (1 : FractionalIdeal B⁰ L) =
      (maximalIdeal B : FractionalIdeal B⁰ L) ^ (-d) := by
    rw [coeIdeal_differentIdeal A K L B] at hd
    calc
      _ = ((dual A K (1 : FractionalIdeal B⁰ L))⁻¹)⁻¹ := (inv_inv _).symm
      _ = ((maximalIdeal B : FractionalIdeal B⁰ L) ^ d)⁻¹ := congrArg Inv.inv hd
      _ = _ := (zpow_neg _ _).symm
  have he : (0 : ℤ) < (maximalIdeal B).ramificationIdx A :=
    Int.natCast_pos.mpr (Ideal.ramificationIdx_pos A (maximalIdeal B))
  rw [maximalIdeal_zpow_eq_spanSingleton A K hπ s,
    traceImage_le_spanSingleton_iff A K _ (zpow_ne_zero s hπK), hdual]
  simp only [map_inv₀, map_zpow₀, hπB]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add₀ hmB,
    maximalIdeal_zpow_le_iff B L, Int.le_ediv_iff_mul_le he]
  rw [mul_comm s ((maximalIdeal B).ramificationIdx A : ℤ)]
  omega

/-- The trace of the `r`-th maximal-ideal power is exactly the power with exponent
`floor ((r + d) / e)`, where `d` is the exponent of the actual different. -/
theorem traceImage_maximalIdeal_zpow (r d : ℤ)
    (hd : (differentIdeal A B : FractionalIdeal B⁰ L) =
      (maximalIdeal B : FractionalIdeal B⁰ L) ^ d) :
    traceImage A K ((maximalIdeal B : FractionalIdeal B⁰ L) ^ r) =
      (maximalIdeal A : FractionalIdeal A⁰ K) ^
        ((r + d) / ((maximalIdeal B).ramificationIdx A : ℤ)) := by
  have hmB : (maximalIdeal B : FractionalIdeal B⁰ L) ≠ 0 :=
    coeIdeal_ne_zero.mpr (IsDiscreteValuationRing.not_a_field B)
  have htrace := traceImage_ne_zero A K (zpow_ne_zero r hmB)
  obtain ⟨t, ht⟩ := existsUnique_fractionalIdeal_eq_maximalIdeal_zpow A K htrace
  apply le_antisymm
  · exact (traceImage_maximalIdeal_zpow_le_iff A K B L r _ d hd).mpr le_rfl
  · rw [ht.1, maximalIdeal_zpow_le_iff A K]
    exact (traceImage_maximalIdeal_zpow_le_iff A K B L r t d hd).mp ht.1.le

/-- The exact trace formula with its different exponent extracted from Mathlib's
actual different ideal, without a supplied exponent or trace-image assumption. -/
theorem traceImage_maximalIdeal_zpow_count (r : ℤ) :
    traceImage A K ((maximalIdeal B : FractionalIdeal B⁰ L) ^ r) =
      (maximalIdeal A : FractionalIdeal A⁰ K) ^
        ((r + FractionalIdeal.count L (maximalSpectrum B)
          (differentIdeal A B : FractionalIdeal B⁰ L)) /
            ((maximalIdeal B).ramificationIdx A : ℤ)) := by
  have hd : (differentIdeal A B : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [coeIdeal_differentIdeal A K L B]
    exact inv_ne_zero (dual_ne_zero A K one_ne_zero)
  exact traceImage_maximalIdeal_zpow A K B L r _
    (fractionalIdeal_eq_maximalIdeal_zpow B L hd)

end RamificationTheory.DiscreteValuationRing
