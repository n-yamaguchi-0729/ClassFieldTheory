/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldInvariantClass
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PicardLangNorm

/-!
# Norms of actual geometric Picard classes over finite fields

For arithmetic Frobenius, every zero-norm class has a periodic primitive.
A fixed class is a norm from the period-n classes exactly when its degree is
divisible by n. All Lang and degree-one inputs are constructed from the curve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra

namespace JacobianVarieties.Picard

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

local notation "φ" =>
  M.constantSemilinearAction c eC heC (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Actual arithmetic Frobenius has periodic primitives for all zero-norm Picard classes. -/
theorem exists_constantFrobenius_periodic_picard_primitive
    (n : ℕ) (hn : n ≠ 0) (x : Pic Ω F)
    (hx : (∑ i ∈ Finset.range n, φ ^ i • x) = 0) :
    ∃ y : Pic Ω F, φ ^ n • y = y ∧ φ • y - y = x := by
  apply H1Gm.exists_periodic_primitive_of_pic0_lang φ _ n hn x hx
  simpa only [pow_one] using
    pic0_constantFrobenius_pow_sub_surjective c M eC heC 1 Nat.one_ne_zero

/-- The only obstruction to an actual periodic geometric Picard norm is degree modulo n. -/
theorem exists_constantFrobenius_periodic_picard_norm_iff
    (n : ℕ) (hn : n ≠ 0) (x : Pic Ω F) (hx : φ • x = x) :
    (∃ y : Pic Ω F, φ ^ n • y = y ∧ ∑ i ∈ Finset.range n, φ ^ i • y = x) ↔
      (n : ℤ) ∣ H1Gm.degree Ω F x := by
  obtain ⟨D, hdeg, hD⟩ := exists_constantFrobenius_fixed_degree_one_class c M eC heC
  have hfixed : φ • H1Gm.mk D = H1Gm.mk D := by
    apply sub_eq_zero.mp
    change H1Gm.mk (φ • D - D) = 0
    exact (QuotientAddGroup.eq_zero_iff (φ • D - D)).mpr hD
  exact H1Gm.exists_periodic_norm_preimage_iff_of_pic0_lang φ n
    (pic0_constantFrobenius_pow_sub_surjective c M eC heC n hn)
    (H1Gm.mk D) hfixed hdeg x hx

end JacobianVarieties.Picard
