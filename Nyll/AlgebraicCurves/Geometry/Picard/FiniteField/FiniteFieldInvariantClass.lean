/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldConstantAction
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.LangFixedClass
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.Models.ConstantExtension.FixedDivisor

/-!
# A Frobenius-invariant geometric divisor class of degree one

Lang surjectivity adjusts a geometric degree-one divisor to a class fixed by
the actual constant-field Frobenius. Periodic Hilbert 90 then gives an exactly
fixed divisor of degree one. No rational point on the original curve is required.
Identification with divisors over the finite field is a separate step.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra

namespace JacobianVarieties.Picard

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- The actual geometric Picard group has a degree-one class fixed by arithmetic Frobenius. -/
theorem exists_constantFrobenius_fixed_degree_one_class
    {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase) :
    ∃ D : Divisor Ω F, Divisor.degree D = 1 ∧
      (M.constantSemilinearAction c eC heC
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) • D - D).IsPrincipal := by
  let g := M.constantSemilinearAction c eC heC (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
  have hLang : Function.Surjective (fun z : Pic0 Ω F => g • z - z) := by
    simpa only [pow_one] using
      pic0_constantFrobenius_pow_sub_surjective c M eC heC 1 Nat.one_ne_zero
  obtain ⟨p⟩ := M.nonempty_rationalPoint
  obtain ⟨D, hdeg, hfixed⟩ := exists_fixed_divisor_class_of_pic0_lang g hLang
    (Finsupp.single (M.pointEquivPlace p) 1)
  refine ⟨D, ?_, hfixed⟩
  rw [hdeg, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, one_mul]

/-- Arithmetic Frobenius fixes an actual geometric divisor of degree one. -/
theorem exists_constantFrobenius_fixed_degree_one_divisor
    {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase) :
    ∃ D : Divisor Ω F, Divisor.degree D = 1 ∧
      M.constantSemilinearAction c eC heC
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) • D = D := by
  obtain ⟨D, hdeg, hclass⟩ := exists_constantFrobenius_fixed_degree_one_class c M eC heC
  obtain ⟨E, -, hEdeg, hEfixed⟩ := M.exists_constantFrobenius_fixed_divisor c eC heC D hclass
  exact ⟨E, hEdeg.trans hdeg, hEfixed⟩

end JacobianVarieties.Picard
