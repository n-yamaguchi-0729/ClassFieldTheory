/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseEmbedding
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve

/-!
# Actual function-field embeddings in constant towers

The embeddings coming from the two curve projections compose to the embedding
from the direct geometric base change. This follows from the actual pullback
square and functoriality on generic stalks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
open AlgebraicCurve.CurveModel.GalPtSol
open CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
open AlgebraicCurve.CurveModel.ModelIndepSol

namespace AlgebraicCurve.CurveModel

variable {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (E : Type) [Field E] [Algebra k E] [Algebra E Ω] [IsScalarTower k E Ω]

local notation "CE" => pullback c (specMap k E)
local notation "cE" => pullback.snd c (specMap k E)

/-- The concrete embeddings agree for iterated and direct extension of constants. -/
theorem constantBaseEmbedding_tower (x : C.functionField) :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    M.constantBaseEmbedding cE (M.constantTowerModelIso k E Ω c e)
        ((ofSmoothProperCurve cE).constantBaseEmbedding c (Iso.refl _) x) =
      M.constantBaseEmbedding c e x := by
  intro alg
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω c e
  let p₁ := (Iso.refl ME.C).hom ≫ pullback.fst c (specMap k E)
  let p₂ := eE.hom ≫ pullback.fst cE (specMap E Ω)
  have hp : p₂ ≫ p₁ = e.hom ≫ pullback.fst c (specMap k Ω) := by
    change ((e.hom ≫ (Scheme.constantBaseChangeTowerIso k E Ω c).inv) ≫
      pullback.fst cE (specMap E Ω)) ≫ (𝟙 _ ≫ pullback.fst c (specMap k E)) = _
    rw [Category.id_comp, Category.assoc, Category.assoc,
      ← Scheme.constantBaseChangeTowerIso_fst,
      (Scheme.constantBaseChangeTowerIso k E Ω c).inv_hom_id_assoc]
  have h₁ := ME.constantProjection_generic c (Iso.refl _)
  have h₂ := M.constantProjection_generic cE eE
  change M.ffEquiv.symm (FunctionFieldPull.pull p₂ h₂ (FunctionFieldPull.pull p₁ h₁ x)) =
    M.ffEquiv.symm (FunctionFieldPull.pull (e.hom ≫ pullback.fst c (specMap k Ω))
      (M.constantProjection_generic c e) x)
  apply congrArg M.ffEquiv.symm
  have h := FunctionFieldPull.pull_comp p₂ p₁ h₂ h₁
  have hcongr (f g : M.C ⟶ C) (hfg : f = g)
      (hf : f.base (genericPoint M.C) ⤳ genericPoint C)
      (hg : g.base (genericPoint M.C) ⤳ genericPoint C) :
      FunctionFieldPull.pull f hf = FunctionFieldPull.pull g hg := by
    subst g
    rfl
  exact (congrArg (fun f : C.functionField ⟶ M.C.functionField => f x) h).symm.trans
    (congrArg (fun f : C.functionField ⟶ M.C.functionField => f x)
      (hcongr _ _ hp _ _))

end AlgebraicCurve.CurveModel
