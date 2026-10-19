/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
import Nyll.SchemeTheory.Modules.Functoriality.PushforwardRestrict
/-! Local freeness of a pushforward can be checked on Cartesian neighborhoods. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback

open AlgebraicGeometry.Scheme.Modules

section iso
variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

/-- The pullback along the isomorphism identified with pushforward along its inverse. -/
noncomputable def pullbackIsoPushforwardInv : Scheme.Modules.pullback e.hom ≅ pushforward e.inv :=
  (pullbackPushforwardAdjunction e.hom).leftAdjointUniq (pushforwardIsoEquivalence
      e).symm.toAdjunction

end iso

theorem
 _root_.AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X' ⟶
        W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        Scheme.Modules.IsLocallyFreeOfRank n
          ((Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj F))) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by
  apply IsLocallyFreeOfRank.of_forall_exists_opens
  intro y
  obtain ⟨W, hy, W', X', e, π', g', hcart₀, hLF⟩ := h y
  have hcart : IsPullback g' (π' ≫ e.hom) π W.ι :=
    hcart₀.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id])
  refine ⟨W, hy, ?_⟩
  have hres := isPullback_morphismRestrict π W
  let θ : X' ≅ (π ⁻¹ᵁ W).toScheme := IsPullback.isoIsPullback _ _ hcart hres.flip
  have hθ₁ : θ.hom ≫ (π ⁻¹ᵁ W).ι = g' := IsPullback.isoIsPullback_hom_fst _ _ hcart hres.flip
  have hθ₂ : θ.hom ≫ (π ∣_ W) = π' ≫ e.hom := IsPullback.isoIsPullback_hom_snd _ _ hcart hres.flip
  have h1 : IsLocallyFreeOfRank n ((pushforward (π' ≫ e.hom)).obj ((Scheme.Modules.pullback g').obj
      F)) := by
    have := hLF.pullback e.inv
    refine IsLocallyFreeOfRank.of_iso ?_ this
    exact ((pullbackIsoPushforwardInv e.symm).app _) ≪≫ ((pushforwardComp π' e.hom).app _)
  have h2 : IsLocallyFreeOfRank n ((pushforward (π ∣_ W)).obj ((Scheme.Modules.pullback (π ⁻¹ᵁ
      W).ι).obj F)) := by
    have h1' : IsLocallyFreeOfRank n
        ((pushforward (θ.hom ≫ (π ∣_ W))).obj ((Scheme.Modules.pullback (θ.hom ≫ (π ⁻¹ᵁ W).ι)).obj
            F)) := by
      refine IsLocallyFreeOfRank.of_iso ?_ h1
      exact (pushforwardCongr hθ₂.symm).app _ ≪≫ (pushforward _).mapIso ((pullbackCongr
          hθ₁.symm).app _)
    refine IsLocallyFreeOfRank.of_iso ?_ h1'
    refine ((pushforwardComp θ.hom (π ∣_ W)).symm.app _) ≪≫ (pushforward (π ∣_ W)).mapIso ?_
    refine (pushforward θ.hom).mapIso ((pullbackComp θ.hom (π ⁻¹ᵁ W).ι).symm.app F) ≪≫ ?_
    have : (Scheme.Modules.pullback θ.hom).IsEquivalence := by
      have : (pushforward θ.inv).IsEquivalence := (pushforwardIsoEquivalence
          θ.symm).isEquivalence_functor
      exact Functor.isEquivalence_of_iso (pullbackIsoPushforwardInv θ).symm
    exact (asIso ((pullbackPushforwardAdjunction θ.hom).unit.app ((Scheme.Modules.pullback (π ⁻¹ᵁ
        W).ι).obj F))).symm
  refine IsLocallyFreeOfRank.of_iso ?_ h2
  exact (pushforward (π ∣_ W)).mapIso ((restrictFunctorIsoPullback (π ⁻¹ᵁ W).ι).symm.app F) ≪≫
    (pushforwardRestrictIso π W).app F ≪≫ (restrictFunctorIsoPullback W.ι).app _

end Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
