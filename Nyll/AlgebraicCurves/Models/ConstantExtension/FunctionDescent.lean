/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardDescent
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseIsRational
import Nyll.GaloisCohomology.FieldTheory.PeriodicSubfield

/-!
# The actual fixed field of geometric Frobenius

Descend the principal divisor of a fixed function. Descent of principality gives
an original rational function with the same geometric divisor; their ratio is
a fixed constant and therefore belongs to the original finite field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- A geometric rational function is fixed by Frobenius exactly when it is defined over the base. -/
theorem constantFrobenius_fixed_iff_mem_original (hC : ConstantsAreBase k F₀) (x : F) :
    let _ : Algebra F₀ F := M₀.constantModelAlgebra M e
    φ • x = x ↔ x ∈ Set.range (algebraMap F₀ F) := by
  intro baseAlg
  have hfix (a : F₀) : φ • algebraMap F₀ F a = algebraMap F₀ F a :=
    M.constantSemilinearAction_baseEmbedding M₀.toBase e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (M₀.ffEquiv a)
  constructor
  · intro hxfix
    by_cases hx : x = 0
    · exact ⟨0, (map_zero _).trans hx.symm⟩
    let unitAction : MulDistribMulAction (SemilinearAut Ω F) Fˣ := Units.mulDistribMulActionRight
    let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
    have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
    obtain ⟨hInt, hgen⟩ := M₀.constantModel_isIntegral_and_adjoin M e he
    let u := Units.mk0 x hx
    let D := Divisor.principalHom (K := Ω) (Additive.ofMul u)
    have hu : φ • u = u := Units.ext hxfix
    have hDfix : φ • D = D := by
      exact (Divisor.principalHom_smul φ (Additive.ofMul u)).symm.trans
        (congrArg (fun z : Fˣ => Divisor.principalHom (K := Ω) (Additive.ofMul z)) hu)
    obtain ⟨D₀, hD₀, -⟩ := M₀.existsUnique_constantFrobenius_divisor_descent M e he hC D hDfix
    have hPr : (Divisor.pullbackConstants Ω F D₀).IsPrincipal := by
      rw [hD₀]
      exact ⟨x, hx, Divisor.principalHom_apply (Additive.ofMul u)⟩
    obtain ⟨f, hf, hDf⟩ :=
      Divisor.isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension hgen hC hPr
    have hy : algebraMap F₀ F f ≠ 0 :=
      (map_ne_zero_iff (algebraMap F₀ F) (algebraMap F₀ F).injective).mpr hf
    have hord (w : Place Ω F) : w.ord (x / algebraMap F₀ F f) = 0 := by
      rw [div_eq_mul_inv, w.ord_mul hx (inv_ne_zero hy), w.ord_inv, ← sub_eq_add_neg]
      apply sub_eq_zero.mpr
      exact (Divisor.principalHom_apply (Additive.ofMul u) w).symm.trans
        ((congrArg (fun E : Divisor Ω F => E w) hD₀).symm.trans
          (Divisor.pullbackConstants_apply_eq_ord hDf w))
    obtain ⟨p⟩ := M.nonempty_rationalPoint
    let v := M.pointEquivPlace p
    have hΩ : ConstantsAreBase Ω F := constantsAreBase_of_exists_isRational v
      ((Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v))
      (by rw [IsCurveOver.deg_eq_one_of_isAlgClosed]; exact Nat.one_ne_zero)
    have hratio : x / algebraMap F₀ F f ∈ LSpace (0 : Divisor Ω F) := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro w
      rw [Finsupp.zero_apply, neg_zero, hord]
    rw [hΩ] at hratio
    obtain ⟨a, ha⟩ := hratio
    change algebraMap Ω F a = x / algebraMap F₀ F f at ha
    have hafix : FiniteField.frobeniusAlgEquivOfAlgebraic k Ω a = a := by
      apply (algebraMap Ω F).injective
      have hsem := SemilinearAut.smul_algebraMap φ a
      rw [M.constantSemilinearAction_baseAut] at hsem
      change φ • algebraMap Ω F a =
        algebraMap Ω F (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω a) at hsem
      rw [← hsem, ha, smul_div₀', hxfix, hfix]
    obtain ⟨b, hb⟩ := (FiniteField.frobenius_eq_self_iff_mem_range k Ω a).mp hafix
    refine ⟨algebraMap k F₀ b * f, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply k F₀ F,
      IsScalarTower.algebraMap_apply k Ω F, hb, ha]
    exact div_mul_cancel₀ x hy
  · rintro ⟨a, rfl⟩
    exact hfix a

/-- The actual original function field is the fixed field of geometric Frobenius. -/
def constantFrobeniusFixedFieldEquiv (hC : ConstantsAreBase k F₀) :
    F₀ ≃+* RingAut.periodicSubfield (SemilinearAut.toRingAut φ) 1 := by
  let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
  let j : F₀ →+* RingAut.periodicSubfield (SemilinearAut.toRingAut φ) 1 :=
    (algebraMap F₀ F).codRestrict _ (fun a => by
      change ((SemilinearAut.toRingAut φ) ^ 1) (algebraMap F₀ F a) = algebraMap F₀ F a
      rw [pow_one]
      exact (M₀.constantFrobenius_fixed_iff_mem_original M e he hC _).mpr ⟨a, rfl⟩)
  refine RingEquiv.ofBijective j ⟨j.injective, ?_⟩
  intro x
  have hx : φ • (x : F) = x := by
    have h := x.property
    change ((SemilinearAut.toRingAut φ) ^ 1) (x : F) = x at h
    rw [SemilinearAut.smul_def]
    simpa only [pow_one] using h
  obtain ⟨a, ha⟩ := (M₀.constantFrobenius_fixed_iff_mem_original M e he hC x).mp hx
  exact ⟨a, Subtype.ext ha⟩

end AlgebraicCurve.CurveModel
