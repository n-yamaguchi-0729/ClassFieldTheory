/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.DivisorPeriod
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseIsRational
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusUnits

/-!
# Positive constant-field Frobenius periods of rational functions

A period of the principal divisor makes the quotient of a function and its
Frobenius translate a constant. Multiplicative Lang on the algebraic constants
removes this quotient. A common period then fixes the original function.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve CyclicAction

namespace AlgebraicCurve.CurveModel

attribute [local instance] Units.mulDistribMulActionRight
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M : CurveModel Ω F) {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c] [IsSeparated c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

/-- Every rational function has a positive period for the actual constant-field Frobenius. -/
theorem exists_constantFrobenius_function_period (x : F) :
    ∃ n : ℕ, n ≠ 0 ∧
      (M.constantSemilinearAction c e he (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ^ n •
        x = x := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  let g := M.constantSemilinearAction c e he σ
  by_cases hx : x = 0
  · exact ⟨1, Nat.one_ne_zero, hx ▸ smul_zero (g ^ 1)⟩
  let u : Fˣ := Units.mk0 x hx
  obtain ⟨n, hn, hD⟩ := M.exists_constantFrobenius_divisor_period c e he
    (Divisor.principalHom (K := Ω) (Additive.ofMul u))
  have hzero : Divisor.principalHom (K := Ω) (Additive.ofMul ((g ^ n • u) / u)) = 0 := by
    change Divisor.principalHom (K := Ω)
      (Additive.ofMul (g ^ n • u) - Additive.ofMul u) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((Divisor.principalHom_smul (g ^ n) (Additive.ofMul u)).trans hD)
  obtain ⟨p⟩ := M.nonempty_rationalPoint
  let v := M.pointEquivPlace p
  have hC : ConstantsAreBase Ω F := constantsAreBase_of_exists_isRational v
    ((Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v))
    (by rw [IsCurveOver.deg_eq_one_of_isAlgClosed]; exact Nat.one_ne_zero)
  obtain ⟨z, hz⟩ := (Divisor.principalHom_eq_zero_iff hC
    (Additive.ofMul ((g ^ n • u) / u))).mp hzero
  have hzx : (g ^ n • x) / x = algebraMap Ω F (z : Ω) := by
    have h := (congrArg Units.val hz).symm
    change ((g ^ n • u : Fˣ) / u : Fˣ).val = algebraMap Ω F (z : Ω) at h
    rw [Units.val_div_eq_div_val] at h
    exact h
  obtain ⟨a, ha⟩ := FiniteField.exists_unit_frobenius_pow_div k Ω n hn z
  have haf : (σ ^ n) (a : Ω) / (a : Ω) = (z : Ω) := by
    have h := congrArg Units.val ha
    rw [Units.val_div_eq_div_val] at h
    change (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n) (a : Ω) / (a : Ω) =
      (z : Ω) at h
    exact h
  have hgconst (i : ℕ) (r : Ω) :
      g ^ i • algebraMap Ω F r = algebraMap Ω F ((σ ^ i) r) := by
    change (M.constantSemilinearAction c e he σ) ^ i • algebraMap Ω F r = _
    rw [← map_pow, SemilinearAut.smul_algebraMap, M.constantSemilinearAction_baseAut]
    rfl
  let b := algebraMap Ω F (a : Ω)
  have hb : b ≠ 0 := (map_ne_zero_iff (algebraMap Ω F) (algebraMap Ω F).injective).mpr a.ne_zero
  have hzb : (g ^ n • b) / b = algebraMap Ω F (z : Ω) := by
    rw [show g ^ n • b = algebraMap Ω F ((σ ^ n) (a : Ω)) from hgconst n a,
      ← map_div₀, haf]
  have hfixed : g ^ n • (x / b) = x / b := by
    rw [smul_div₀', (div_eq_iff hx).mp hzx, (div_eq_iff hb).mp hzb]
    exact mul_div_mul_left x b
      ((map_ne_zero_iff (algebraMap Ω F) (algebraMap Ω F).injective).mpr z.ne_zero)
  obtain ⟨m, hm, ham⟩ := FiniteField.exists_frobenius_period k Ω (a : Ω)
  have hbm : g ^ m • b = b := (hgconst m a).trans (congrArg (algebraMap Ω F) ham)
  have hxn : g ^ (n * m) • (x / b) = x / b :=
    periodicSubgroup_le_mul g n m hfixed
  have hbn : g ^ (n * m) • b = b := by
    rw [Nat.mul_comm]
    exact periodicSubgroup_le_mul g m n hbm
  refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
  calc
    g ^ (n * m) • x = g ^ (n * m) • ((x / b) * b) :=
      congrArg (fun y : F => g ^ (n * m) • y) (div_mul_cancel₀ x hb).symm
    _ = x := by rw [smul_mul', hxn, hbn, div_mul_cancel₀ x hb]

end AlgebraicCurve.CurveModel
