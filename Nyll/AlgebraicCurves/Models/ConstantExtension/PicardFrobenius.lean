/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.FiniteFrobenius
import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardTower
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantSemilinear

/-!
# Frobenius equivariance of the actual Picard comparison

The finite Galois generator and the geometric Frobenius intertwine under
the actual function-field embedding, hence also under actual Picard pullback.
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

/-- Pullback intertwines the actual finite and geometric Frobenius actions on Picard classes. -/
theorem constantPicardBaseChange_finiteFrobenius :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E (CE).functionField,
      (ofSmoothProperCurve cE).constantPicardBaseChange M
          (M.constantTowerModelIso k E Ω M₀.toBase e)
          (M.constantTowerModelIso_base k E Ω M₀.toBase e he)
          (M₀.constantFiniteSemilinearFrobenius M e he E • x) =
        φ • (ofSmoothProperCurve cE).constantPicardBaseChange M
          (M.constantTowerModelIso k E Ω M₀.toBase e)
          (M.constantTowerModelIso_base k E Ω M₀.toBase e he) x := by
  intro algE x
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  let baseAlg : Algebra (CE).functionField F := ME.constantModelAlgebra M eE
  let constAlg : Algebra E F := ((algebraMap Ω F).comp (algebraMap E Ω)).toAlgebra
  have towerΩ : IsScalarTower E Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerE : IsScalarTower E (CE).functionField F :=
    ME.constantModel_isScalarTower M eE heE
  have hInt : Algebra.IsIntegral (CE).functionField F :=
    (ME.constantModel_isIntegral_and_adjoin M eE heE).1
  change Pic.baseChange E Ω (CE).functionField F
      (M₀.constantFiniteSemilinearFrobenius M e he E • x) =
    φ • Pic.baseChange E Ω (CE).functionField F x
  apply SemilinearAut.baseChange_smul
  intro y
  exact (M₀.constantFiniteFrobenius_geometric M e he E y).symm

/-- The arithmetic-periodic Picard comparison preserves the generator action. -/
theorem constantPicardPeriodicEquiv_finiteFrobenius :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E (CE).functionField,
      (M₀.constantPicardPeriodicEquiv M e he E
          (M₀.constantFiniteSemilinearFrobenius M e he E • x) : Pic Ω F) =
        φ • (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) := by
  intro algE x
  rw [constantPicardPeriodicEquiv_apply, constantPicardPeriodicEquiv_apply]
  exact M₀.constantPicardBaseChange_finiteFrobenius M e he E x

end AlgebraicCurve.CurveModel
