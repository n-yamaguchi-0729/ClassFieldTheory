/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.RigidifiedBundleIsoMapPullbackRigSectionCompEq
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleUniqueAppEqSmul
import Mathlib.Util.WithWeakNamespace

/-!
Prove uniqueness of isomorphisms respecting rigidifications when the base-change map on global
sections is surjective.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite

open
  RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.AlgebraicGeometry.Scheme.Modules

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
with_weak_namespace _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hp : Function.Surjective (pullback.snd c t).appTop)
    (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit
      T.ringCatSheaf)
    (φ ψ : M.L ≅ M'.L)
    (hφ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α)
    (hψ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso ψ ≪≫ α' = α) :
    φ = ψ := by
  have hep : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
  have hF : (Scheme.Modules.pullback (rigSection c t ε)).map φ.hom =
      (Scheme.Modules.pullback (rigSection c t ε)).map ψ.hom := by
    have h := congrArg Iso.hom (hφ.trans hψ.symm)
    change (Scheme.Modules.pullback (rigSection c t ε)).map φ.hom ≫ α'.hom =
      (Scheme.Modules.pullback (rigSection c t ε)).map ψ.hom ≫ α'.hom at h
    exact (Iso.cancel_iso_hom_right _ _ α').mp h
  have hγ : (Scheme.Modules.pullback (rigSection c t ε)).map (φ.hom ≫ ψ.inv) = 𝟙 _ := by
    rw [Functor.map_comp, hF, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  obtain ⟨s, hs, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul M.isInvertible (φ.hom
      ≫ ψ.inv)
  have hγs : φ.hom ≫ ψ.inv = smulHom s M.L := by
    ext U x
    exact hs U x
  have h1 : (rigSection c t ε).appTop s = 1 := by
    have h := hγ
    rw [hγs, pullback_map_smulHom] at h
    have h' : smulHom ((rigSection c t ε).appTop s) (SheafOfModules.unit T.ringCatSheaf) =
        𝟙 (SheafOfModules.unit T.ringCatSheaf) := by
      have hc := smulHom_comp ((rigSection c t ε).appTop s) α.hom
      erw [h, Category.id_comp] at hc
      apply (Iso.cancel_iso_hom_left α _ _).mp
      exact hc.symm.trans (Category.comp_id α.hom).symm
    have h'' := congrArg (fun u => toΓ (Scheme.Modules.Hom.app u ⊤ (unitOne ⊤))) h'
    simp only [smulHom_app_apply, resTop_top] at h''
    have h3 : ((rigSection c t ε).appTop s * 1 : Γ(T, ⊤)) = 1 := h''
    simpa using h3
  obtain ⟨d, hd⟩ := hp s
  have hd1 : d = 1 := by
    rw [← appTop_appTop_of_comp_eq_id _ _ hep d, hd, h1]
  have hs1 : s = 1 := by rw [← hd, hd1, map_one]
  rw [hs1, smulHom_one] at hγs
  ext : 1
  simpa using hγs =≫ ψ.hom
end RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
