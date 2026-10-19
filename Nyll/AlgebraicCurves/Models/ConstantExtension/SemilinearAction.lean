/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.FunctionFields.FunctionFieldAutomorphisms
import Nyll.SchemeTheory.Morphisms.ConstantTwist

/-!
# The actual action of constant-field automorphisms

Pullback along coefficient twists gives a group homomorphism into semilinear
function-field automorphisms. The construction retains the two projections
and the formula on actual germs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
open AlgebraicCurve.CurveModel.GalPtSol

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    (e : M.C ≅ pullback c (specMap k Ω))

/-- The actual coefficient twist transported to the chosen curve model. -/
def coefficientIso (σ : Ω ≃ₐ[k] Ω) : M.C ≅ M.C :=
  e ≪≫ Scheme.constantTwist c σ ≪≫ e.symm

/-- The coefficient action fixes the original curve projection. -/
theorem coefficientIso_fst (σ : Ω ≃ₐ[k] Ω) :
    (M.coefficientIso c e σ).hom ≫ e.hom ≫ pullback.fst c (specMap k Ω) =
      e.hom ≫ pullback.fst c (specMap k Ω) := by
  simp only [coefficientIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    e.inv_hom_id_assoc, Scheme.constantTwist_fst]

/-- The coefficient action composes in the same order as pullback of rational functions. -/
theorem coefficientIso_mul (σ τ : Ω ≃ₐ[k] Ω) :
    M.coefficientIso c e (σ * τ) = M.coefficientIso c e σ ≪≫ M.coefficientIso c e τ := by
  apply Iso.ext
  simp only [coefficientIso, Scheme.constantTwist_mul, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, e.inv_hom_id_assoc]

/-- The identity coefficient automorphism acts identically on the curve model. -/
theorem coefficientIso_one : M.coefficientIso c e (1 : Ω ≃ₐ[k] Ω) = Iso.refl M.C := by
  apply Iso.ext
  simp only [coefficientIso, Scheme.constantTwist_one, Iso.trans_hom, Iso.symm_hom,
    Iso.refl_hom, Category.id_comp, e.hom_inv_id]

variable (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

include he in
/-- The base projection is twisted by the specified coefficient automorphism. -/
theorem coefficientIso_base (σ : Ω ≃ₐ[k] Ω) :
    (M.coefficientIso c e σ).hom ≫ M.toBase =
      M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  change (e.hom ≫ (Scheme.constantTwist c σ).hom ≫ e.inv) ≫ M.toBase = _
  rw [Category.assoc, Category.assoc, ← he, e.inv_hom_id_assoc,
    Scheme.constantTwist_snd, ← Category.assoc, he]

/-- The actual homomorphism from coefficient automorphisms to semilinear field automorphisms. -/
def constantSemilinearAction : (Ω ≃ₐ[k] Ω) →* SemilinearAut Ω F where
  toFun σ := gSL M (M.coefficientIso c e σ) σ.toRingEquiv (M.coefficientIso_base c e he σ)
  map_one' := by
    apply SemilinearAut.toRingAut_injective
    change M.functionFieldAut (M.coefficientIso c e (1 : Ω ≃ₐ[k] Ω)) = 1
    rw [coefficientIso_one, functionFieldAut_refl]
  map_mul' σ τ := by
    apply SemilinearAut.toRingAut_injective
    change M.functionFieldAut (M.coefficientIso c e (σ * τ)) =
      M.functionFieldAut (M.coefficientIso c e σ) * M.functionFieldAut (M.coefficientIso c e τ)
    rw [coefficientIso_mul, functionFieldAut_trans]

/-- The constructed semilinear action has precisely the prescribed action on constants. -/
theorem constantSemilinearAction_baseAut (σ : Ω ≃ₐ[k] Ω) :
    SemilinearAut.baseAut (M.constantSemilinearAction c e he σ) = σ.toRingEquiv := rfl

/-- The constructed action agrees with pullback of actual rational-function germs. -/
theorem constantSemilinearAction_germ (σ : Ω ≃ₐ[k] Ω)
    (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
    [Nonempty (Scheme.Opens.toScheme ((M.coefficientIso c e σ).hom ⁻¹ᵁ U))]
    (t : Γ(M.C, U)) :
    M.constantSemilinearAction c e he σ • M.ffEquiv.symm (M.C.germToFunctionField U t) =
      M.ffEquiv.symm (M.C.germToFunctionField ((M.coefficientIso c e σ).hom ⁻¹ᵁ U)
        (((M.coefficientIso c e σ).hom.app U).hom t)) :=
  germ_clause M (M.coefficientIso c e σ) σ.toRingEquiv (M.coefficientIso_base c e he σ) U t

end AlgebraicCurve.CurveModel
