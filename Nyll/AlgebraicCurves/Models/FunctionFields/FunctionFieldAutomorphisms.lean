/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearActionUniqueness
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace

/-!
# Functorial function-field automorphisms

Expose the function-field pullback attached to actual curve automorphisms and
its composition law. Germ formulas identify it with any compatible semilinear
action, avoiding choices of an unrelated field automorphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
open AlgebraicCurve.CurveModel.GalPtSol
open CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
open AlgebraicCurve.CurveModel.ModelIndepSol

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {K F : Type} [Field K] [Field F] [Algebra K F] (M : CurveModel K F)

/-- The actual pullback of rational functions along a curve automorphism. -/
def functionFieldAut (θ : M.C ≅ M.C) : F ≃+* F := gRingEquiv M θ

/-- Pullback of functions respects the composition order of ring automorphisms. -/
theorem functionFieldAut_trans (θ ψ : M.C ≅ M.C) :
    M.functionFieldAut (θ ≪≫ ψ) = M.functionFieldAut θ * M.functionFieldAut ψ := by
  apply RingEquiv.ext
  intro z
  change M.ffEquiv.symm (FunctionFieldPull.equivOfIso (θ ≪≫ ψ) (M.ffEquiv z)) =
    M.ffEquiv.symm (FunctionFieldPull.equivOfIso θ
      (M.ffEquiv (M.ffEquiv.symm (FunctionFieldPull.equivOfIso ψ (M.ffEquiv z)))))
  rw [M.ffEquiv.apply_symm_apply]
  apply congrArg M.ffEquiv.symm
  exact congrArg (fun a : M.C.functionField ⟶ M.C.functionField => a (M.ffEquiv z))
    (FunctionFieldPull.pull_comp θ.hom ψ.hom
      (FunctionFieldPull.specializes_of_iso θ) (FunctionFieldPull.specializes_of_iso ψ))

/-- The identity curve automorphism induces the identity field automorphism. -/
theorem functionFieldAut_refl : M.functionFieldAut (Iso.refl M.C) = 1 := by
  apply RingEquiv.ext
  intro z
  change M.ffEquiv.symm (FunctionFieldPull.pull (𝟙 M.C)
    (specializes_refl _) (M.ffEquiv z)) = z
  rw [FunctionFieldPull.pull_id]
  exact M.ffEquiv.symm_apply_apply z

/-- A semilinear action satisfying the actual germ formula induces this same field pullback. -/
theorem toRingAut_eq_functionFieldAut (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hb : θ.hom ≫ M.toBase = M.toBase ≫
      Spec.map (CommRingCat.ofHom (SemilinearAut.baseAut g).toRingHom))
    (hg : ∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
      g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t))) :
    SemilinearAut.toRingAut g = M.functionFieldAut θ :=
  congrArg SemilinearAut.toRingAut
    (M.semilinearAut_eq_of_germ_action θ g (gSL M θ (SemilinearAut.baseAut g) hb)
      hg (germ_clause M θ (SemilinearAut.baseAut g) hb))

end AlgebraicCurve.CurveModel
