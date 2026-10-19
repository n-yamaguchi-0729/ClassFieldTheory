/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.GenericPointMemPreimageCompPullbackFst

/-!
# The original function field inside a constant base change

The actual curve projection embeds the original function field. Its stalk
formula and coefficient invariance connect geometric Frobenius to divisor descent.
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

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k))
    (e : M.C ≅ pullback c (specMap k Ω))

/-- The actual projection to the original curve sends the generic point to its generic point. -/
theorem constantProjection_generic :
    (e.hom ≫ pullback.fst c (specMap k Ω)).base (genericPoint M.C) ⤳ genericPoint C := by
  rw [specializes_iff_forall_open]
  intro U hU hx
  exact genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
    (algebraMap k Ω).injective c e.hom ⟨U, hU⟩ ⟨genericPoint C, hx⟩

/-- The field embedding induced by the actual projection to the original curve. -/
def constantBaseEmbedding : C.functionField →+* F :=
  M.ffEquiv.symm.toRingHom.comp
    (FunctionFieldPull.pull (e.hom ≫ pullback.fst c (specMap k Ω))
      (M.constantProjection_generic c e)).hom

/-- The projection embedding agrees with pullback on every actual stalk. -/
theorem constantBaseEmbedding_stalk (x : M.C)
    (s : C.presheaf.stalk ((e.hom ≫ pullback.fst c (specMap k Ω)).base x)) :
    M.constantBaseEmbedding c e (algebraMap
      (C.presheaf.stalk ((e.hom ≫ pullback.fst c (specMap k Ω)).base x)) C.functionField s) =
      M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x) M.C.functionField
        (((e.hom ≫ pullback.fst c (specMap k Ω)).stalkMap x).hom s)) :=
  congrArg M.ffEquiv.symm (FunctionFieldPull.pull_algebraMap
    (e.hom ≫ pullback.fst c (specMap k Ω)) (M.constantProjection_generic c e) x s)

variable (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

include he in
/-- Pullback respects the specified inclusion of the original constant field. -/
theorem constantBaseEmbedding_constants (a : k) :
    M.constantBaseEmbedding c e (baseToFunctionField c a) =
      algebraMap Ω F (algebraMap k Ω a) := by
  let p := e.hom ≫ pullback.fst c (specMap k Ω)
  have hp : p ≫ c = M.toBase ≫ specMap k Ω := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hΓ : (specMap k Ω).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (algebraMap k Ω a) := by
    exact (congrArg (fun f => f.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k Ω)))).symm
  change M.ffEquiv.symm (FunctionFieldPull.pull p (M.constantProjection_generic c e)
    (C.presheaf.germ ⊤ (genericPoint C) (TopologicalSpace.Opens.mem_top _)
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)))) = _
  rw [FunctionFieldPull.pull_germ]
  have happ := congrArg (fun f : M.C ⟶ Spec (CommRingCat.of k) =>
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) hp
  change M.ffEquiv.symm (M.C.presheaf.germ ⊤ (genericPoint M.C)
    (TopologicalSpace.Opens.mem_top _) ((p ≫ c).appTop.hom _)) = _
  rw [happ]
  change M.ffEquiv.symm (M.C.presheaf.germ ⊤ (genericPoint M.C)
    (TopologicalSpace.Opens.mem_top _) (M.toBase.appTop.hom ((specMap k Ω).appTop.hom _))) = _
  rw [hΓ]
  change M.ffEquiv.symm (baseToFunctionField M.toBase (algebraMap k Ω a)) = _
  rw [← M.ffEquiv_algebraMap, M.ffEquiv.symm_apply_apply]

/-- Every coefficient automorphism fixes the embedded original function field. -/
theorem constantSemilinearAction_baseEmbedding (σ : Ω ≃ₐ[k] Ω) (x : C.functionField) :
    M.constantSemilinearAction c e he σ • M.constantBaseEmbedding c e x =
      M.constantBaseEmbedding c e x := by
  change M.ffEquiv.symm (FunctionFieldPull.equivOfIso (M.coefficientIso c e σ)
    (M.ffEquiv (M.ffEquiv.symm
      (FunctionFieldPull.pull (e.hom ≫ pullback.fst c (specMap k Ω))
        (M.constantProjection_generic c e) x)))) = _
  rw [M.ffEquiv.apply_symm_apply, FunctionFieldPull.equivOfIso_apply]
  apply congrArg M.ffEquiv.symm
  have h := FunctionFieldPull.pull_comp (M.coefficientIso c e σ).hom
    (e.hom ≫ pullback.fst c (specMap k Ω))
    (FunctionFieldPull.specializes_of_iso (M.coefficientIso c e σ))
    (M.constantProjection_generic c e)
  have h' := congrArg (fun f : C.functionField ⟶ M.C.functionField => f x) h
  simpa only [M.coefficientIso_fst, CommRingCat.comp_apply] using h'.symm

end AlgebraicCurve.CurveModel
