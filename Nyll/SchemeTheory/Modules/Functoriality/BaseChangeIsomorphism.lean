/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
import Nyll.SchemeTheory.Modules.Functoriality.PullbackUnitComposition
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Nyll.SchemeTheory.Modules.OpenImmersionUnit
import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeComposition
import Nyll.SchemeTheory.Modules.LocalMorphisms

/-!
# Independence of a Cartesian presentation of base change

The isomorphism property of a module base-change comparison is independent of the
chosen scheme realizing the same Cartesian square.
-/

section isIso_baseChangeHom_iff_of_isPullback

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem invE5_inv_app_map_eqToHom_id_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁
    W₃ : Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ 𝟙 _ ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom
        e).op := by
  subst e
  simp only [eqToHom_refl, op_id, P.presheaf.map_id, Q.presheaf.map_id, Category.id_comp,
    ← Scheme.Modules.Hom.comp_app, c.inv_hom_id, Scheme.Modules.Hom.id_app]

theorem invE5_baseChangeHom_iso_comp {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X} (θ : X₁ ≅ X₂) (h₂ : g₂ ≫ π = π₂ ≫ ψ)
    (h₁ : (θ.hom ≫ g₂) ≫ π = (θ.hom ≫ π₂) ≫ ψ) (F : X.Modules) :
    baseChangeHom h₁ F =
      baseChangeHom h₂ F ≫ (pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
          ((Modules.pullback g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
            g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F) := by
  apply pullback_hom_ext_of_unit_app ψ
  intro U
  have e₁ : ((θ.hom ≫ π₂) ≫ ψ) ⁻¹ᵁ U = ((θ.hom ≫ g₂) ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π₂ ≫ ψ) ⁻¹ᵁ U = (g₂ ≫ π) ⁻¹ᵁ U := by rw [h₂]
  have e₂θ : θ.hom ⁻¹ᵁ ((π₂ ≫ ψ) ⁻¹ᵁ U) = θ.hom ⁻¹ᵁ ((g₂ ≫ π) ⁻¹ᵁ U) := by rw [h₂]
  rw [unit_app_app_comp_baseChangeHom_app π ψ (θ.hom ≫ π₂) (θ.hom ≫ g₂) h₁ F U]
  change _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  have t2 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g₂).unit.app F).app
      (π ⁻¹ᵁ U) ≫ ((Modules.pullback g₂).obj F).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π₂ g₂ h₂ F U
  change _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [t2]
  have u : ((Modules.pullback g₂).obj F).presheaf.map (eqToHom e₂).op ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ
      (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj
      F)).app (g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj
      F)).presheaf.map (eqToHom e₂θ).op :=
    ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).mapPresheaf.naturality (eqToHom e₂).op
  change _ = ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ (((Modules.pullback
      g₂).obj F).presheaf.map (eqToHom e₂).op ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [u]
  have s3 : ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (g₂ ⁻¹ᵁ
      (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv θ.hom g₂ F (π ⁻¹ᵁ U)
  change _ = (((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (g₂ ⁻¹ᵁ
      (π ⁻¹ᵁ U))) ≫ ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map
      (eqToHom e₂θ).op ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [← s3]
  have fin : ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op
      ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)) =
      ((Modules.pullback (θ.hom ≫ g₂)).obj F).presheaf.map (eqToHom e₂θ).op :=
    invE5_inv_app_map_eqToHom_id_hom_app ((pullbackComp θ.hom g₂).app F) e₂θ
  change _ = ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫
      (((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback
      θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op ≫ 𝟙 _ ≫
      ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)))
  erw [fin]
  rfl

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
    {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₁ : X₁ ⟶ T'} {g₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X}
    (h₁ : IsPullback g₁ π₁ π ψ) (h₂ : IsPullback g₂ π₂ π ψ) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom h₁.w F) ↔ IsIso (Scheme.Modules.baseChangeHom h₂.w F) := by
  obtain ⟨θ, hθg, hθπ⟩ : ∃ θ : X₁ ≅ X₂, θ.hom ≫ g₂ = g₁ ∧ θ.hom ≫ π₂ = π₁ :=
    ⟨h₁.isoIsPullback _ _ h₂, IsPullback.isoIsPullback_hom_fst _ _ h₁ h₂,
        IsPullback.isoIsPullback_hom_snd _ _ h₁ h₂⟩
  subst hθg
  subst hθπ
  rw [invE5_baseChangeHom_iso_comp θ h₂.w h₁.w F]
  have : (pushforward θ.hom).IsEquivalence := (pushforwardIsoEquivalence
      θ).isEquivalence_functor
  have i0 : IsIso ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F))
      := inferInstance
  have i1 : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F))) :=
    Functor.map_isIso _ _
  have i2 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj
      ((Modules.pullback g₂).obj F))) :=
    inferInstance
  have i3 : IsIso ((pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    Functor.map_isIso _ _
  have i23 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj
      ((Modules.pullback g₂).obj F)) ≫
      (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i2 i3
  have iW : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)) ≫
      (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
          g₂).obj F)) ≫
        (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i23
  constructor
  · intro h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (baseChangeHom h₂.w F)
      ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback
          g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
            g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) iW h
  · intro h
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h iW

end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isIso_baseChangeHom_iff_of_isPullback

section isIso_baseChangeHom_of_isOpenImmersion

/-!
# Base change along open immersions

The module base change comparison for a pullback square with an open immersion
is an isomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isOpenImmersion
    {X T Y S : Scheme.{u}} {π : X ⟶ T} {j : S ⟶ T} [IsOpenImmersion j] {ρ : Y ⟶ S} {u : Y ⟶ X}
    (hu : IsPullback u ρ π j) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom hu.w F) := by
  have : IsOpenImmersion u := by
    rw [show u = hu.isoPullback.hom ≫ pullback.fst π j from hu.isoPullback_hom_fst.symm]
    infer_instance
  have hrange : ∀ U : T.Opens, U ≤ j.opensRange → π ⁻¹ᵁ U ≤ u.opensRange := by
    intro U hU x hx
    obtain ⟨s, hs⟩ := hU hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := j) x s hs.symm
    refine ⟨hu.isoPullback.inv.base z, ?_⟩
    change (hu.isoPullback.inv ≫ u).base z = x
    rw [hu.isoPullback_inv_fst]
    exact hz
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  suffices h : ∀ W : S.Opens, W = j ⁻¹ᵁ (j ''ᵁ V) → IsIso ((Scheme.Modules.baseChangeHom hu.w F).app
      W) from
    h V (j.preimage_image_eq V).symm
  intro W hW
  subst hW
  have hUle : j ''ᵁ V ≤ j.opensRange := j.image_le_opensRange V
  have i1 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange j _ _ hUle)
  have i2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app F).app (π ⁻¹ᵁ (j ''ᵁ
      V))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange u F _ (hrange _ hUle))
  have key := Scheme.Modules.unit_app_app_comp_baseChangeHom_app π j ρ u hu.w F (j ''ᵁ V)
  have hc : IsIso ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ≫
        (Scheme.Modules.baseChangeHom hu.w F).app (j ⁻¹ᵁ (j ''ᵁ V))) := by
    rw [key]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ i2 ?_
    first
      | exact Functor.map_isIso _ _
      | exact @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_op _)
  exact IsIso.of_isIso_comp_left (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
    ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ((Scheme.Modules.baseChangeHom hu.w
        F).app (j ⁻¹ᵁ (j ''ᵁ V)))
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
end ProofImplementation

end isIso_baseChangeHom_of_isOpenImmersion

section isIso_baseChangeHom_of_forall_exists_isPullback

/-!
# Local Cartesian tests for the base-change comparison

The base-change comparison is an isomorphism when it is an isomorphism on compatible
Cartesian presentations over neighbourhoods of every point of the new base.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem n2E5_isIso_baseChangeHom_congr_bottom {X T X' T' : Scheme.{u}} {π : X ⟶ T} {π' : X' ⟶
    T'} {g' : X' ⟶ X}
    {b b' : T' ⟶ T} (eb : b = b') (h : g' ≫ π = π' ≫ b) (h' : g' ≫ π = π' ≫ b') (F : X.Modules) :
    IsIso (baseChangeHom h F) ↔ IsIso (baseChangeHom h' F) := by
  subst eb
  exact Iff.rfl

theorem n2E5_isIso_app_of_isIso_pullback_map {T' S' : Scheme.{u}} (j : S' ⟶ T') [IsOpenImmersion j]
    {M N : T'.Modules} (β : M ⟶ N) (hβ : IsIso ((Scheme.Modules.pullback j).map β))
    (V : T'.Opens) (hV : V ≤ j.opensRange) :
    IsIso (β.app V) := by
  have n := congrArg (fun t => Scheme.Modules.Hom.app t V) ((pullbackPushforwardAdjunction
      j).unit.naturality β)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
      Scheme.Modules.Hom.comp_app] at n
  have i1 : IsIso (((pullbackPushforwardAdjunction j).unit.app M).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_unit_app_of_le_opensRange j M V hV)
  have i2 : IsIso (((pullbackPushforwardAdjunction j).unit.app N).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_unit_app_of_le_opensRange j N V hV)
  have i3 : IsIso (((pushforward j).map ((Scheme.Modules.pullback j).map β)).app V) :=
    (Hom.isIso_iff_isIso_app.mp hβ) _
  have hc : IsIso ((((pullbackPushforwardAdjunction j).unit.app M).app V) ≫
      ((pushforward j).map ((Scheme.Modules.pullback j).map β)).app V) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i3
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ i2 hc n

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) (F : X.Modules)
    (h : ∀ y : T', ∃ (W : T.Opens) (W' : T'.Opens) (_ : y ∈ W') (S S' Y Y' : Scheme.{u})
      (e : S ≅ W.toScheme) (e' : S' ≅ W'.toScheme) (φ : S' ⟶ S)
      (_ : (e'.hom ≫ W'.ι) ≫ ψ = φ ≫ e.hom ≫ W.ι)
      (ρ : Y ⟶ S) (u : Y ⟶ X) (_ : IsPullback u ρ π (e.hom ≫ W.ι))
      (ρ' : Y' ⟶ S') (v : Y' ⟶ Y) (hv : IsPullback v ρ' ρ φ),
      IsIso (Scheme.Modules.baseChangeHom hv.w ((Scheme.Modules.pullback u).obj F))) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) := by
  choose W W' hy S S' Y Y' e e' φ heq ρ u hu ρ' v hv hiso using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top _ W' ?_ ?_
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  intro y V hVle
  have : IsOpenImmersion ((e' y).hom ≫ (W' y).ι) := inferInstance
  have : IsOpenImmersion ((e y).hom ≫ (W y).ι) := inferInstance
  have sqj := IsPullback.of_hasPullback π' ((e' y).hom ≫ (W' y).ι)
  have hbig : IsPullback (pullback.fst π' ((e' y).hom ≫ (W' y).ι) ≫ g') (pullback.snd π' ((e'
      y).hom ≫ (W' y).ι))
      π (((e' y).hom ≫ (W' y).ι) ≫ ψ) := sqj.paste_horiz hcart
  have ph1 := baseChangeHom_comp_horizontal hcart.w sqj.w hbig.w F
  have ioi1 : IsIso (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F)) :=
    isIso_baseChangeHom_of_isOpenImmersion sqj ((Scheme.Modules.pullback g').obj F)
  have hvu : IsPullback (v y ≫ u y) (ρ' y) π (((e' y).hom ≫ (W' y).ι) ≫ ψ) := by
    rw [heq y]
    exact (hv y).paste_horiz (hu y)
  have h12 : (v y ≫ u y) ≫ π = ρ' y ≫ (φ y ≫ (e y).hom ≫ (W y).ι) := ((hv y).paste_horiz (hu y)).w
  have ph2 := baseChangeHom_comp_horizontal (hu y).w (hv y).w h12 F
  have ioi2 : IsIso (baseChangeHom (hu y).w F) := isIso_baseChangeHom_of_isOpenImmersion (hu y) F
  have : IsIso (baseChangeHom (hv y).w ((Scheme.Modules.pullback (u y)).obj F)) := hiso y
  have hA : IsIso (baseChangeHom h12 F) := by
    rw [ph2]
    have j1 : IsIso ((pullbackComp (φ y) ((e y).hom ≫ (W y).ι)).inv.app ((pushforward π).obj F))
        := inferInstance
    have j2 : IsIso ((Scheme.Modules.pullback (φ y)).map (baseChangeHom (hu y).w F)) :=
      @Functor.map_isIso _ _ _ _ _ _ _ _ ioi2
    have j3 : IsIso (baseChangeHom (hv y).w ((Scheme.Modules.pullback (u y)).obj F)) := hiso y
    have j4 : IsIso ((pushforward (ρ' y)).map ((pullbackComp (v y) (u y)).hom.app F)) :=
        Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ j1 (@IsIso.comp_isIso _ _ _ _ _ _ _ j2
        (@IsIso.comp_isIso _ _ _ _ _ _ _ j3 j4))
  have hB : IsIso (baseChangeHom hvu.w F) :=
    (n2E5_isIso_baseChangeHom_congr_bottom (heq y).symm h12 hvu.w F).mp hA
  have hC : IsIso (baseChangeHom hbig.w F) := (isIso_baseChangeHom_iff_of_isPullback hbig hvu
      F).mpr hB
  have hD : IsIso ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map
      (baseChangeHom hcart.w F)) := by
    rw [ph1] at hC
    have h1 := IsIso.of_isIso_comp_left ((pullbackComp ((e' y).hom ≫ (W' y).ι) ψ).inv.app
        ((pushforward π).obj F))
      ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map (baseChangeHom hcart.w F) ≫
        baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
          (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
            ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F))
    have k2 : IsIso ((pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
        ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) :=
            Functor.map_isIso _ _
    have k12 : IsIso (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
        (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
          ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ ioi1 k2
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map (baseChangeHom hcart.w F))
      (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
        (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
          ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) k12 h1
  have hVr : V ≤ ((e' y).hom ≫ (W' y).ι).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    exact hVle
  exact n2E5_isIso_app_of_isIso_pullback_map ((e' y).hom ≫ (W' y).ι) (baseChangeHom hcart.w F)
      hD V hVr

end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isIso_baseChangeHom_of_forall_exists_isPullback
