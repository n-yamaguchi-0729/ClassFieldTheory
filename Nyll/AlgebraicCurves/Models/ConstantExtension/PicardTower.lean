/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardDescent
import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelConstants
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField

/-!
# Arithmetic Picard groups over finite constant extensions

Construct the curve model on the actual finite base change. Its constants are
full by geometric descent, and its Picard group identifies with the periodic
geometric Picard classes for the corresponding power of the original Frobenius.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve CyclicAction

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase] (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)
    (E : Type) [Field E] [Fintype E] [Algebra k E] [Algebra E Ω]
    [IsScalarTower k E Ω] [Algebra.IsAlgebraic E Ω]

local notation "CE" => pullback M₀.toBase (specMap k E)
local notation "cE" => pullback.snd M₀.toBase (specMap k E)
local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Actual finite-base-change Picard groups are the corresponding Frobenius-periodic classes. -/
def constantPicardPeriodicEquiv :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    Pic E (CE).functionField ≃+
      periodicSubgroup (A := Pic Ω F) φ (Module.finrank k E) := by
  intro alg
  have hcurve : IsCurveOver E (CE).functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType E (CE).functionField := essFiniteType_functionField cE
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  have hC : ConstantsAreBase E (CE).functionField :=
    ME.constantsAreBase_of_constantModel M eE heE
  let ψ := M.constantSemilinearAction ME.toBase eE heE
    (FiniteField.frobeniusAlgEquivOfAlgebraic E Ω)
  have hψ : ψ = φ ^ Module.finrank k E :=
    M.constantSemilinearAction_frobenius_tower k E Ω M₀.toBase e he
  have hsub : periodicSubgroup (A := Pic Ω F) ψ 1 =
      periodicSubgroup (A := Pic Ω F) φ (Module.finrank k E) := by
    rw [hψ]
    ext x
    change ((φ ^ Module.finrank k E) ^ 1 • x = x) ↔ _
    rw [pow_one]
    rfl
  exact (ME.constantPicardFixedEquiv M eE heE hC).trans (AddEquiv.addSubgroupCongr hsub)

/-- The comparison is the actual Picard pullback along the curve projection. -/
theorem constantPicardPeriodicEquiv_apply :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E (CE).functionField,
      (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) =
        (ofSmoothProperCurve cE).constantPicardBaseChange M
          (M.constantTowerModelIso k E Ω M₀.toBase e)
          (M.constantTowerModelIso_base k E Ω M₀.toBase e he) x := by
  intro alg x
  rfl

/-- Finite-base-change comparison preserves the arithmetic divisor degree. -/
theorem degree_constantPicardPeriodicEquiv :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : IsCurveOver E (CE).functionField :=
      isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
        (RingEquiv.refl _) (fun _ => rfl)
    ∀ x : Pic E (CE).functionField,
      H1Gm.degree Ω F (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) =
        H1Gm.degree E (CE).functionField x := by
  intro alg hcurve x
  have hft : Algebra.EssFiniteType E (CE).functionField := essFiniteType_functionField cE
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  have hC : ConstantsAreBase E (CE).functionField :=
    ME.constantsAreBase_of_constantModel M eE heE
  rw [constantPicardPeriodicEquiv_apply]
  exact ME.degree_constantPicardBaseChange M eE heE hC x

end AlgebraicCurve.CurveModel
