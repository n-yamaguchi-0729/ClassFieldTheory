/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelExtension
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseIsRational
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusUnits

/-!
# Full constants from an actual integral geometric model

A function without poles remains without poles after extending constants.
On the geometric curve it is constant, and its Frobenius invariance forces
that constant into the original finite field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F₀ F : Type} [Field k] [Finite k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

include he in
/-- An integral geometric base change ensures that the original finite constants are full. -/
theorem constantsAreBase_of_constantModel : ConstantsAreBase k F₀ := by
  let : Fintype k := Fintype.ofFinite k
  let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
  let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  have hInt : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
  let φ := M.constantSemilinearAction M₀.toBase e he
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
  have hfix (x : F₀) : φ • algebraMap F₀ F x = algebraMap F₀ F x :=
    M.constantSemilinearAction_baseEmbedding M₀.toBase e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (M₀.ffEquiv x)
  obtain ⟨p⟩ := M.nonempty_rationalPoint
  let v := M.pointEquivPlace p
  have hΩ : ConstantsAreBase Ω F := constantsAreBase_of_exists_isRational v
    ((Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v))
    (by rw [IsCurveOver.deg_eq_one_of_isAlgClosed]; exact Nat.one_ne_zero)
  refine le_antisymm ?_ (fun x hx => ?_)
  · intro x hx
    by_cases hx0 : x = 0
    · exact hx0 ▸ zero_mem _
    have hxord := (mem_lSpace_iff_ord.mp hx).resolve_left hx0
    have hgeom : algebraMap F₀ F x ∈ LSpace (0 : Divisor Ω F) := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro w
      rw [Finsupp.zero_apply, neg_zero, Place.ord_restrictConstants (K := k) w x]
      exact mul_nonneg (Int.natCast_nonneg _) (by
        simpa only [Finsupp.zero_apply, neg_zero] using hxord (Place.restrictConstants F₀ w))
    rw [hΩ] at hgeom
    obtain ⟨a, ha⟩ := hgeom
    change algebraMap Ω F a = algebraMap F₀ F x at ha
    have hafix : FiniteField.frobeniusAlgEquivOfAlgebraic k Ω a = a := by
      apply (algebraMap Ω F).injective
      have hsem := SemilinearAut.smul_algebraMap φ a
      rw [M.constantSemilinearAction_baseAut] at hsem
      change φ • algebraMap Ω F a =
        algebraMap Ω F (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω a) at hsem
      rw [← hsem, ha, hfix]
    obtain ⟨b, hb⟩ := (FiniteField.frobenius_eq_self_iff_mem_range k Ω a).mp hafix
    refine ⟨b, ?_⟩
    change algebraMap k F₀ b = x
    apply (algebraMap F₀ F).injective
    rw [← IsScalarTower.algebraMap_apply k F₀ F, IsScalarTower.algebraMap_apply k Ω F, hb, ha]
  · obtain ⟨a, ha⟩ := hx
    exact ha ▸ algebraMap_mem_lSpace_zero a

end AlgebraicCurve.CurveModel
