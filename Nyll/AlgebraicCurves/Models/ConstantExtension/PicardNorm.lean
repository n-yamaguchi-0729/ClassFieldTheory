/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardFrobenius
import Nyll.AlgebraicCurves.Divisors.Norm.PicardNormBaseChange
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PicardNormConstants
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindexBaseChange

/-!
# Comparing actual arithmetic and geometric Picard norms

The norm is actual divisor pushforward after reindexing the extended constants.
Its geometric pullback equals the sum of powers of the actual Frobenius action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase] (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)
    (E : Type) [Field E] [Fintype E] [Algebra k E] [Algebra E Ω]
    [IsScalarTower k E Ω] [Algebra.IsAlgebraic E Ω]

local notation "CE" => pullback M₀.toBase (specMap k E)
local notation "cE" => pullback.snd M₀.toBase (specMap k E)
local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
local notation "σ" => SemilinearAut.toRingAut φ
local notation "d" => Module.finrank k E

/-- The actual arithmetic norm from the finite constant base change. -/
def constantPicardNorm :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    Pic E (CE).functionField →+ Pic k F₀ := by
  intro algE
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let constAlg : Algebra k (CE).functionField :=
    ((algebraMap E (CE).functionField).comp (algebraMap k E)).toAlgebra
  have towerE : IsScalarTower k E (CE).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let alg₀ : Algebra F₀ (CE).functionField := M₀.constantModelAlgebra ME (Iso.refl _)
  have tower₀ : IsScalarTower k F₀ (CE).functionField :=
    M₀.constantModel_isScalarTower ME (Iso.refl _) (Category.id_comp _)
  obtain ⟨hfin, hgal, -⟩ := M₀.constantFiniteExtension_properties M e he E
  have hcurve : IsCurveOver E (CE).functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hprincipal : HasPrincipalDivisors k (CE).functionField :=
    FunctionField.hasPrincipalDivisors_of_extendedConstants k E (CE).functionField
  exact Pic.normConstants k E F₀ (CE).functionField

/-- The actual Picard norm becomes the geometric Frobenius sum under actual pullback. -/
theorem constantPicardBaseChange_norm :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E (CE).functionField,
      M₀.constantPicardBaseChange M e he (M₀.constantPicardNorm M e he E x) =
        ∑ i ∈ Finset.range d, φ ^ i •
          (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) := by
  intro algE x
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let constAlg : Algebra k (CE).functionField :=
    ((algebraMap E (CE).functionField).comp (algebraMap k E)).toAlgebra
  have towerE : IsScalarTower k E (CE).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let alg₀ : Algebra F₀ (CE).functionField := M₀.constantModelAlgebra ME (Iso.refl _)
  have tower₀ : IsScalarTower k F₀ (CE).functionField :=
    M₀.constantModel_isScalarTower ME (Iso.refl _) (Category.id_comp _)
  obtain ⟨hfin, hgal, -⟩ := M₀.constantFiniteExtension_properties M e he E
  have hcurve : IsCurveOver E (CE).functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hprincipal : HasPrincipalDivisors k (CE).functionField :=
    FunctionField.hasPrincipalDivisors_of_extendedConstants k E (CE).functionField
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  let algF₀ : Algebra F₀ F := M₀.constantModelAlgebra M e
  let algFE : Algebra (CE).functionField F := ME.constantModelAlgebra M eE
  let algkF : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  let algEF : Algebra E F := ((algebraMap Ω F).comp (algebraMap E Ω)).toAlgebra
  have towerkΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerEΩ : IsScalarTower E Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerk₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  have towerEE : IsScalarTower E (CE).functionField F := ME.constantModel_isScalarTower M eE heE
  have towerFields : IsScalarTower F₀ (CE).functionField F := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (M.constantBaseEmbedding_tower M₀.toBase e E (M₀.ffEquiv a)).symm
  have towerkE : IsScalarTower k (CE).functionField F := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply k F₀ F,
      IsScalarTower.algebraMap_apply F₀ (CE).functionField F,
      ← IsScalarTower.algebraMap_apply k F₀ (CE).functionField]
  have hInt₀ : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
  have hIntE : Algebra.IsIntegral (CE).functionField F :=
    (ME.constantModel_isIntegral_and_adjoin M eE heE).1
  let q := (FunctionField.picConstantEquiv k E (CE).functionField).symm x
  change Pic.baseChange k Ω F₀ F (Pic.norm (K := F₀) q) = _
  rw [Pic.baseChange_norm_eq_sum (M₀.constantFiniteFrobenius M e he E)
    (M₀.zpowers_constantFiniteFrobenius_eq_top M e he E) φ
    (fun y => (M₀.constantFiniteFrobenius_geometric M e he E y).symm),
    M₀.orderOf_constantFiniteFrobenius M e he E]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun y : Pic Ω F => φ ^ i • y)
  rw [← FunctionField.baseChange_picConstantEquiv (E := E) q]
  change Pic.baseChange E Ω (CE).functionField F
    ((FunctionField.picConstantEquiv k E (CE).functionField)
      ((FunctionField.picConstantEquiv k E (CE).functionField).symm x)) = _
  rw [AddEquiv.apply_symm_apply, constantPicardPeriodicEquiv_apply]
  rfl

end AlgebraicCurve.CurveModel
