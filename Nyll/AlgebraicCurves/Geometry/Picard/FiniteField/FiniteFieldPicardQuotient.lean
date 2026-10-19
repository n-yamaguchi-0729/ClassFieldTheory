/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldPicardNorm
import Nyll.GaloisCohomology.Cyclic.PeriodicNorm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual periodic geometric Picard norm quotient

Degree modulo n identifies the quotient of Frobenius-fixed geometric Picard
classes by norms of period-n classes with Z/nZ. The periodic norm kernel is
exactly the periodic coboundary image. Descent to arithmetic divisor classes
and to idele classes is not included in this comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra CyclicAction

namespace JacobianVarieties.Picard

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

local notation "φ" =>
  M.constantSemilinearAction c eC heC (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Degree modulo n computes the actual periodic geometric Picard norm quotient. -/
def constantFrobenius_picardNormQuotientEquiv (n : ℕ) (hn : n ≠ 0) :
    (periodicSubgroup (A := Pic Ω F) φ 1 ⧸ (periodicNorm (A := Pic Ω F) φ n).range) ≃+
      ZMod n := by
  apply Classical.choice
  let d : periodicSubgroup (A := Pic Ω F) φ 1 →+ ZMod n :=
    ((Int.castAddHom (ZMod n)).comp (H1Gm.degree Ω F)).comp
      (periodicSubgroup (A := Pic Ω F) φ 1).subtype
  have hker : (periodicNorm (A := Pic Ω F) φ n).range = d.ker := by
    ext x
    have hxpow : φ ^ 1 • (x : Pic Ω F) = x := x.property
    have hx : φ • (x : Pic Ω F) = x := by simpa only [pow_one] using hxpow
    change (∃ y, periodicNorm φ n y = x) ↔ (H1Gm.degree Ω F (x : Pic Ω F) : ZMod n) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← exists_constantFrobenius_periodic_picard_norm_iff c M eC heC n hn x hx]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.property, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  obtain ⟨D, hdeg, hD⟩ := exists_constantFrobenius_fixed_degree_one_class c M eC heC
  have hfixed : φ • H1Gm.mk D = H1Gm.mk D := by
    apply sub_eq_zero.mp
    change H1Gm.mk (φ • D - D) = 0
    exact (QuotientAddGroup.eq_zero_iff (φ • D - D)).mpr hD
  let u : periodicSubgroup (A := Pic Ω F) φ 1 :=
    ⟨H1Gm.mk D, by
      change φ ^ 1 • H1Gm.mk D = H1Gm.mk D
      simpa only [pow_one] using hfixed⟩
  have hdu : d u = 1 := by
    change (Divisor.degree D : ZMod n) = 1
    rw [hdeg, Int.cast_one]
  have hsurj : Function.Surjective d := by
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
    refine ⟨a • u, ?_⟩
    rw [map_zsmul, hdu, zsmul_eq_mul, mul_one]
    exact ha
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective d hsurj)⟩

/-- The periodic geometric Picard norm index equals the constant-field period. -/
theorem natCard_constantFrobenius_picardNormQuotient (n : ℕ) (hn : n ≠ 0) :
    Nat.card (periodicSubgroup (A := Pic Ω F) φ 1 ⧸
      (periodicNorm (A := Pic Ω F) φ n).range) = n := by
  let : NeZero n := ⟨hn⟩
  rw [Nat.card_congr (constantFrobenius_picardNormQuotientEquiv c M eC heC n hn).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- The periodic geometric Picard norm sequence is exact at the norm kernel. -/
theorem constantFrobenius_picard_periodic_exact (n : ℕ) (hn : n ≠ 0) :
    (periodicCoboundary (A := Pic Ω F) φ n).range =
      (periodicNorm (A := Pic Ω F) φ n).ker :=
  range_periodicCoboundary_eq_ker φ n
    (fun x hx => exists_constantFrobenius_periodic_picard_primitive c M eC heC n hn x hx)

end JacobianVarieties.Picard
