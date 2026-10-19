/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
import Nyll.SchemeTheory.Morphisms.ConstantTwistTower
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower

/-!
# Semilinear constant actions in towers

The same geometric function field carries compatible actions over the original
and intermediate constant fields. Arithmetic Frobenius over a finite larger
constant field is the corresponding power of the original action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

variable (k E Ω : Type) [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    {F : Type} [Field F] [Algebra Ω F] (M : CurveModel Ω F)
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    (e : M.C ≅ pullback c (specMap k Ω))

local notation "cE" => pullback.snd c (specMap k E)

/-- The same curve model, identified with the iterated constant base change. -/
def constantTowerModelIso : M.C ≅ pullback cE (specMap E Ω) :=
  e ≪≫ (Scheme.constantBaseChangeTowerIso k E Ω c).symm

/-- The two coefficient twists coincide on the actual geometric curve model. -/
theorem coefficientIso_tower (σ : Ω ≃ₐ[E] Ω) :
    M.coefficientIso cE (M.constantTowerModelIso k E Ω c e) σ =
      M.coefficientIso c e (σ.restrictScalars k) := by
  apply Iso.ext
  simp only [coefficientIso, constantTowerModelIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [← Category.assoc (Scheme.constantTwist cE σ).hom
    (Scheme.constantBaseChangeTowerIso k E Ω c).hom e.inv,
    ← Scheme.constantBaseChangeTowerIso_twist k E Ω c σ]
  simp only [Category.assoc, (Scheme.constantBaseChangeTowerIso k E Ω c).inv_hom_id_assoc]

variable (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

include he in
/-- The transported model still has the same structure map over the final constants. -/
theorem constantTowerModelIso_base :
    (M.constantTowerModelIso k E Ω c e).hom ≫ pullback.snd cE (specMap E Ω) = M.toBase := by
  change (e.hom ≫ (Scheme.constantBaseChangeTowerIso k E Ω c).inv) ≫ _ = _
  rw [Category.assoc, ← Scheme.constantBaseChangeTowerIso_snd k E Ω c,
    (Scheme.constantBaseChangeTowerIso k E Ω c).inv_hom_id_assoc]
  exact he

/-- The actual semilinear actions agree after restricting constants. -/
theorem constantSemilinearAction_tower (σ : Ω ≃ₐ[E] Ω) :
    M.constantSemilinearAction cE (M.constantTowerModelIso k E Ω c e)
        (M.constantTowerModelIso_base k E Ω c e he) σ =
      M.constantSemilinearAction c e he (σ.restrictScalars k) := by
  apply SemilinearAut.toRingAut_injective
  change M.functionFieldAut (M.coefficientIso cE (M.constantTowerModelIso k E Ω c e) σ) =
    M.functionFieldAut (M.coefficientIso c e (σ.restrictScalars k))
  exact congrArg M.functionFieldAut (M.coefficientIso_tower k E Ω c e σ)

/-- Frobenius on an actual geometric function field changes by the finite constant degree. -/
theorem constantSemilinearAction_frobenius_tower [Fintype k] [Fintype E]
    [Algebra.IsAlgebraic k Ω] [Algebra.IsAlgebraic E Ω] :
    M.constantSemilinearAction cE (M.constantTowerModelIso k E Ω c e)
        (M.constantTowerModelIso_base k E Ω c e he)
        (FiniteField.frobeniusAlgEquivOfAlgebraic E Ω) =
      (M.constantSemilinearAction c e he (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ^
        Module.finrank k E := by
  rw [constantSemilinearAction_tower, FiniteField.frobeniusAlgEquiv_restrictScalars, map_pow]

end AlgebraicCurve.CurveModel
