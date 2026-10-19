/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-! Pulling back an affine open is the Cartesian square defined by its section algebra. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem
    _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
    (W : T.Opens) (hW : IsAffineOpen W) :
    let _ : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
    ∃ g' : Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) ⟶ Limits.pullback c t,
      IsPullback g' (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
          (Limits.pullback.snd c t)
        hW.fromSpec ∧
      g' ≫ Limits.pullback.fst c t = Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R
          Γ(T, W)) := by
  intro algebraStructure
  have key : hW.fromSpec ≫ t = specMap R Γ(T, W) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW (le_top (a := W))
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
    change _ = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top).hom)
    rw [CommRingCat.ofHom_hom]
    exact h.symm
  let e₁ : Limits.pullback (Limits.pullback.snd c t) hW.fromSpec ≅ Limits.pullback c (specMap R
      Γ(T, W)) :=
    pullbackLeftPullbackSndIso c t hW.fromSpec ≪≫ Limits.pullback.congrHom rfl key
  have h1 : IsPullback (Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec)
      (Limits.pullback.snd (Limits.pullback.snd c t) hW.fromSpec) (Limits.pullback.snd c t)
          hW.fromSpec :=
    IsPullback.of_hasPullback _ _
  refine ⟨e₁.inv ≫ Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec, ?_, ?_⟩
  swap
  · rw [Category.assoc, Iso.inv_comp_eq]
    simp only [e₁, Iso.trans_hom, Category.assoc, Limits.pullback.congrHom_hom]
    delta CategoryTheory.Limits.pullback.map
    rw [Limits.pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  refine h1.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) ?_
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  simp only [e₁, Iso.trans_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      Limits.pullback.congrHom_hom]
  delta CategoryTheory.Limits.pullback.map
  rw [Limits.pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
