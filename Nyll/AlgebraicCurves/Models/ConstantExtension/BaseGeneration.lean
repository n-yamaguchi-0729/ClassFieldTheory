/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseEmbedding
import Nyll.AlgebraicCurves.Geometry.Schemes.LocalGeometry.RingEquivStalkPullbackLocalizationTensorStalk
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Generation of the actual geometric function field

The stalk description of a scheme pullback as a localized tensor product shows
that constants and the actual original function field generate the geometric field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k))
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

include he in
/-- Constants and pullbacks of original rational functions generate the geometric field. -/
theorem adjoin_constantBaseEmbedding_eq_top :
    IntermediateField.adjoin Ω (Set.range (M.constantBaseEmbedding c e)) = ⊤ := by
  let Y := pullback c (specMap k Ω)
  let η := genericPoint M.C
  let y : Y := e.hom.base η
  let z : C := (pullback.fst c (specMap k Ω)).base y
  let R := C.presheaf.stalk z
  let alg : Algebra k R :=
    ((C.presheaf.germ ⊤ z (TopologicalSpace.Opens.mem_top z)).hom.comp
      (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  obtain ⟨𝔮, h𝔮, l, -, hl, hr⟩ :=
    exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd C c Ω y
  let q : Y.presheaf.stalk y →+* F :=
    M.ffEquiv.symm.toRingHom.comp (e.hom.stalkMap η).hom
  have hqsurj : Function.Surjective q :=
    M.ffEquiv.symm.surjective.comp (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap η)).2
  let S := IntermediateField.adjoin Ω (Set.range (M.constantBaseEmbedding c e))
  have hleft (s : R) : q (((pullback.fst c (specMap k Ω)).stalkMap y).hom s) ∈ S := by
    have h := M.constantBaseEmbedding_stalk c e η s
    change M.constantBaseEmbedding c e (algebraMap R C.functionField s) =
      M.ffEquiv.symm ((M.C.presheaf.stalkSpecializes (specializes_refl η)).hom
        (((e.hom ≫ pullback.fst c (specMap k Ω)).stalkMap η).hom s)) at h
    rw [TopCat.Presheaf.stalkSpecializes_refl, Scheme.Hom.stalkMap_comp] at h
    exact h ▸ IntermediateField.subset_adjoin Ω _
      ⟨algebraMap R C.functionField s, rfl⟩
  have hright (a : Ω) : q (Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top y)
      ((pullback.snd c (specMap k Ω)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a))) ∈ S := by
    have h : q (Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top y)
        ((pullback.snd c (specMap k Ω)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a))) = algebraMap Ω F a := by
      change M.ffEquiv.symm ((e.hom.stalkMap η).hom _) = _
      rw [Scheme.Hom.germ_stalkMap_apply]
      have happ := congrArg (fun f : M.C ⟶ Spec (CommRingCat.of Ω) =>
        f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)) he
      change M.ffEquiv.symm (M.C.presheaf.germ ⊤ η (TopologicalSpace.Opens.mem_top η)
        ((e.hom ≫ pullback.snd c (specMap k Ω)).appTop.hom _)) = _
      rw [happ]
      change M.ffEquiv.symm (baseToFunctionField M.toBase a) = algebraMap Ω F a
      rw [← M.ffEquiv_algebraMap]
      exact M.ffEquiv.symm_apply_apply _
    rw [h]
    exact S.algebraMap_mem a
  let ψ : Localization.AtPrime 𝔮 →+* F := q.comp l.symm.toRingHom
  have hψ (w : Y.presheaf.stalk y) : ψ (l w) = q w := congrArg q (l.symm_apply_apply w)
  have htensor (b : R ⊗[k] Ω) : ψ (algebraMap (R ⊗[k] Ω) (Localization.AtPrime 𝔮) b) ∈ S := by
    induction b using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add]; exact S.add_mem ha hb
    | tmul s a =>
      have hmul : s ⊗ₜ[k] a = (s ⊗ₜ[k] (1 : Ω)) * ((1 : R) ⊗ₜ[k] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hmul, map_mul, map_mul, ← hl, ← hr]
      rw [hψ, hψ]
      exact S.mul_mem (hleft s) (hright a)
  apply top_unique
  intro f _
  obtain ⟨w, rfl⟩ := hqsurj f
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj 𝔮.primeCompl (l w)
  have hb : ψ (algebraMap (R ⊗[k] Ω) (Localization.AtPrime 𝔮) (b : R ⊗[k] Ω)) ≠ 0 :=
    ((IsLocalization.map_units (Localization.AtPrime 𝔮) b).map ψ).ne_zero
  have heq : q w = ψ (algebraMap (R ⊗[k] Ω) (Localization.AtPrime 𝔮) a) /
      ψ (algebraMap (R ⊗[k] Ω) (Localization.AtPrime 𝔮) (b : R ⊗[k] Ω)) := by
    apply (eq_div_iff hb).mpr
    have h := congrArg ψ hab
    rw [map_mul, hψ] at h
    exact h
  rw [heq]
  exact S.div_mem (htensor a) (htensor b)

end AlgebraicCurve.CurveModel
