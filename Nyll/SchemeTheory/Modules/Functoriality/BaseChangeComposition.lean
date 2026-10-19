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
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
import Nyll.SchemeTheory.Modules.Functoriality.PullbackUnitComposition

/-!
# Horizontal composition of base-change comparisons

The module base-change comparison for a composite square agrees with the horizontal
composition of the two comparisons, through the canonical pullback and pushforward maps.
-/

section baseChangeHom_comp_horizontal

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_horizontal

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

theorem phE5_inv_app_map_eqToHom_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁ W₃ :
    Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom e).op
        := by
  subst e
  simp only [eqToHom_refl, op_id, P.presheaf.map_id, Q.presheaf.map_id, Category.id_comp,
    ← Scheme.Modules.Hom.comp_app, c.inv_hom_id, Scheme.Modules.Hom.id_app]

theorem _root_.AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''} {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ))
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂ ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map ((Scheme.Modules.pullbackComp g'' g').hom.app
                F) := by
  apply pullback_hom_ext_of_unit_app (ψ' ≫ ψ)
  intro U
  have e₁ : (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π'' ≫ ψ') ⁻¹ᵁ (ψ ⁻¹ᵁ U) = (g'' ≫ π') ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by rw [h₂]
  have e₁g : g'' ⁻¹ᵁ ((π' ≫ ψ) ⁻¹ᵁ U) = g'' ⁻¹ᵁ ((g' ≫ π) ⁻¹ᵁ U) := by rw [h₁]
  rw [unit_app_app_comp_baseChangeHom_app π (ψ' ≫ ψ) π'' (g'' ≫ g') h₁₂ F U]
  have s0 : ((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U ≫
      ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      ((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv ψ' ψ ((pushforward π).obj F) U
  change _ = (((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U
      ≫ ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫
      ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s0]
  have s1 : ((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ)
      ⁻¹ᵁ U) = (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) := by
    have n := congrArg (fun t => Scheme.Modules.Hom.app t (ψ ⁻¹ᵁ U))
      ((pullbackPushforwardAdjunction ψ').unit.naturality (baseChangeHom h₁ F))
    simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app] at n
    exact n.symm
  change _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ)
      ⁻¹ᵁ U)) ≫ (baseChangeHom h₂ ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s1]
  have t1 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g').unit.app F).app
      (π ⁻¹ᵁ U) ≫ ((Modules.pullback g').obj F).presheaf.map (eqToHom e₁).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π' g' h₁ F U
  change _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t1]
  have t2 : ((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj
      ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((Modules.pullback
      g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g'').unit.app
      ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ ((Modules.pullback g'').obj
      ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π' ψ' π'' g'' h₂ ((Modules.pullback g').obj F) (ψ ⁻¹ᵁ U)
  change _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((Modules.pullback
      g').obj F).presheaf.map (eqToHom e₁).op ≫ (((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t2]
  have u4 : ((Modules.pullback g').obj F).presheaf.map (eqToHom e₁).op ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ
      (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj
      F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj
      F)).presheaf.map (eqToHom e₁g).op :=
    ((pullbackPushforwardAdjunction g'').unit.app
      ((Modules.pullback g').obj F)).mapPresheaf.naturality (eqToHom e₁).op
  change _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ (((Modules.pullback
      g').obj F).presheaf.map (eqToHom e₁).op ≫ ((pullbackPushforwardAdjunction g'').unit.app
      ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ ((Modules.pullback g'').obj
      ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op ≫ ((pullbackComp g''
      g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [u4]
  have s3 : ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (g' ⁻¹ᵁ
      (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv g'' g' F (π ⁻¹ᵁ U)
  change _ = (((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (g' ⁻¹ᵁ
      (π ⁻¹ᵁ U))) ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map
      (eqToHom e₁g).op ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map
      (eqToHom e₂).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [← s3]
  have m : ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      e₁g).op ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      e₂).op = ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      (e₂.trans e₁g)).op :=
    by
      let H : X''.Modules := (Modules.pullback g'').obj ((Modules.pullback g').obj F)
      exact (H.presheaf.map_comp (eqToHom e₁g).op (eqToHom e₂).op).symm.trans
        (congrArg H.presheaf.map (Subsingleton.elim _ _))
  change _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ (((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₁g).op ≫ ((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op) ≫ ((pullbackComp g''
      g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [m]
  have fin : ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom (e₂.trans
      e₁g)).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)) =
      ((Modules.pullback (g'' ≫ g')).obj F).presheaf.map (eqToHom (e₂.trans e₁g)).op :=
    phE5_inv_app_map_eqToHom_hom_app ((pullbackComp g'' g').app F) (e₂.trans e₁g)
  change _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      (((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom (e₂.trans e₁g)).op ≫
      ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)))
  erw [fin]
  rfl

end AlgebraicGeometry.Scheme.Modules
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_horizontal
end ProofImplementation

end baseChangeHom_comp_horizontal

section baseChangeHom_comp_vertical

/-!
# Scheme Modules base Change Hom comp vertical
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_vertical

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

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_vertical
open AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_vertical
    {X Y T X' Y' T' : Scheme.{u}} {ρ : X ⟶ Y} {σ : Y ⟶ T} {ρ' : X' ⟶ Y'} {σ' : Y' ⟶ T'}
    {g' : X' ⟶ X} {k' : Y' ⟶ Y} {ψ : T' ⟶ T}
    (htop : g' ≫ ρ = ρ' ≫ k') (hbot : k' ≫ σ = σ' ≫ ψ) (h : g' ≫ (ρ ≫ σ) = (ρ' ≫ σ') ≫ ψ)
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h F =
      (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pushforwardComp ρ σ).inv.app F) ≫
        Scheme.Modules.baseChangeHom hbot ((Scheme.Modules.pushforward ρ).obj F) ≫
          (Scheme.Modules.pushforward σ').map (Scheme.Modules.baseChangeHom htop F) ≫
            (Scheme.Modules.pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F) :=
              by
  apply pullback_hom_ext_of_unit_app ψ
  intro U
  have eb : (σ' ≫ ψ) ⁻¹ᵁ U = (k' ≫ σ) ⁻¹ᵁ U := by rw [hbot]
  have eb' : ρ' ⁻¹ᵁ ((σ' ≫ ψ) ⁻¹ᵁ U) = ρ' ⁻¹ᵁ ((k' ≫ σ) ⁻¹ᵁ U) := by rw [hbot]
  have et : (ρ' ≫ k') ⁻¹ᵁ (σ ⁻¹ᵁ U) = (g' ≫ ρ) ⁻¹ᵁ (σ ⁻¹ᵁ U) := by rw [htop]
  rw [unit_app_app_comp_baseChangeHom_app (ρ ≫ σ) ψ (ρ' ≫ σ') g' h F U]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    pushforward_map_app]
  change _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫
    ((Scheme.Modules.pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) ≫
    (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom htop F).app ((σ' ≫
    ψ) ⁻¹ᵁ U) ≫ ((pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  have s1 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫
    ((Scheme.Modules.pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) =
    ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app
    U := by
    have n := congrArg (fun t => Scheme.Modules.Hom.app t U)
      ((pullbackPushforwardAdjunction ψ).unit.naturality ((pushforwardComp ρ σ).inv.app F))
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
      Scheme.Modules.Hom.comp_app] at n
    have t : ((pushforwardComp ρ σ).inv.app F).app U ≫ ((pullbackPushforwardAdjunction ψ).unit.app
      ((pushforward σ).obj ((pushforward ρ).obj F))).app U = ((pullbackPushforwardAdjunction
      ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫ ((Scheme.Modules.pullback ψ).map
      ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) := n
    have t2 : ((pushforwardComp ρ σ).inv.app F).app U = 𝟙 _ := rfl
    rw [t2] at t
    erw [Category.id_comp] at t
    exact t.symm
  have tb : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj
    F))).app U ≫ (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U) =
    ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫
    ((Scheme.Modules.pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op :=
    unit_app_app_comp_baseChangeHom_app σ ψ σ' k' hbot ((pushforward ρ).obj F) U
  have u3 : ((Scheme.Modules.pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op
    ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U) = (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U) ≫
    ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom eb').op :=
    (baseChangeHom htop F).mapPresheaf.naturality (eqToHom eb).op
  have tt : ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫
    (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g').unit.app
    F).app (ρ ⁻¹ᵁ (σ ⁻¹ᵁ U)) ≫ ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom et).op :=
    unit_app_app_comp_baseChangeHom_app ρ k' ρ' g' htop F (σ ⁻¹ᵁ U)
  have hpc : ((pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F)).app (ψ ⁻¹ᵁ U) =
    𝟙 _ := rfl
  have m : ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom et).op ≫
    ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom eb').op ≫ 𝟙 _ =
    ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom (eb'.trans et)).op :=
    by
      let H : X'.Modules := (Scheme.Modules.pullback g').obj F
      rw [Category.comp_id]
      exact (H.presheaf.map_comp (eqToHom et).op (eqToHom eb').op).symm.trans
        (congrArg H.presheaf.map (Subsingleton.elim _ _))
  let V0 : Ab.{u} := Γ(F, ρ ⁻¹ᵁ (σ ⁻¹ᵁ U))
  let V1 : Ab.{u} := Γ((Scheme.Modules.pullback ψ).obj ((pushforward (ρ ≫ σ)).obj F),
    ψ ⁻¹ᵁ U)
  let V2 : Ab.{u} := Γ((Scheme.Modules.pullback ψ).obj
    ((pushforward σ).obj ((pushforward ρ).obj F)), ψ ⁻¹ᵁ U)
  let V3 : Ab.{u} := Γ((Scheme.Modules.pullback k').obj ((pushforward ρ).obj F),
    (σ' ≫ ψ) ⁻¹ᵁ U)
  let V4 : Ab.{u} := Γ((Scheme.Modules.pullback g').obj F, ρ' ⁻¹ᵁ ((σ' ≫ ψ) ⁻¹ᵁ U))
  let V5 : Ab.{u} := Γ((Scheme.Modules.pullback k').obj ((pushforward ρ).obj F),
    (k' ≫ σ) ⁻¹ᵁ U)
  let V6 : Ab.{u} := Γ((Scheme.Modules.pullback g').obj F, ρ' ⁻¹ᵁ ((k' ≫ σ) ⁻¹ᵁ U))
  let V7 : Ab.{u} := Γ((Scheme.Modules.pullback g').obj F, (g' ≫ ρ) ⁻¹ᵁ (σ ⁻¹ᵁ U))
  let p01 : V0 ⟶ V1 :=
    ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U
  let p12 : V1 ⟶ V2 :=
    ((Scheme.Modules.pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U)
  let p23 : V2 ⟶ V3 :=
    (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U)
  let p34 : V3 ⟶ V4 := (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U)
  let p44 : V4 ⟶ V4 :=
    ((pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  let p02 : V0 ⟶ V2 :=
    ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app U
  let p05 : V0 ⟶ V5 :=
    ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U)
  let p53 : V5 ⟶ V3 :=
    ((Scheme.Modules.pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op
  let p56 : V5 ⟶ V6 := (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U)
  let p64 : V6 ⟶ V4 := ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom eb').op
  let p07 : V0 ⟶ V7 :=
    ((pullbackPushforwardAdjunction g').unit.app F).app (ρ ⁻¹ᵁ (σ ⁻¹ᵁ U))
  let p76 : V7 ⟶ V6 := ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom et).op
  let p74 : V7 ⟶ V4 :=
    ((Scheme.Modules.pullback g').obj F).presheaf.map (eqToHom (eb'.trans et)).op
  have hs1 : p01 ≫ p12 = p02 := s1
  have htb : p02 ≫ p23 = p05 ≫ p53 := tb
  have hu3 : p53 ≫ p34 = p56 ≫ p64 := u3
  have htt : p05 ≫ p56 = p07 ≫ p76 := tt
  have hid : p44 = 𝟙 V4 := hpc
  have hm : p76 ≫ p64 ≫ 𝟙 V4 = p74 := m
  have chain : p01 ≫ p12 ≫ p23 ≫ p34 ≫ p44 = p07 ≫ p74 := by
    calc
      p01 ≫ p12 ≫ p23 ≫ p34 ≫ p44 =
          (p01 ≫ p12) ≫ p23 ≫ p34 ≫ p44 :=
        (Category.assoc p01 p12 (p23 ≫ p34 ≫ p44)).symm
      _ = p02 ≫ p23 ≫ p34 ≫ p44 :=
        congrArg (fun q : V0 ⟶ V2 => q ≫ p23 ≫ p34 ≫ p44) hs1
      _ = (p02 ≫ p23) ≫ p34 ≫ p44 :=
        (Category.assoc p02 p23 (p34 ≫ p44)).symm
      _ = (p05 ≫ p53) ≫ p34 ≫ p44 :=
        congrArg (fun q : V0 ⟶ V3 => q ≫ p34 ≫ p44) htb
      _ = p05 ≫ p53 ≫ p34 ≫ p44 := Category.assoc p05 p53 (p34 ≫ p44)
      _ = p05 ≫ ((p53 ≫ p34) ≫ p44) :=
        congrArg (fun q : V5 ⟶ V4 => p05 ≫ q) (Category.assoc p53 p34 p44).symm
      _ = p05 ≫ ((p56 ≫ p64) ≫ p44) :=
        congrArg (fun q : V5 ⟶ V4 => p05 ≫ (q ≫ p44)) hu3
      _ = p05 ≫ p56 ≫ p64 ≫ p44 :=
        congrArg (fun q : V5 ⟶ V4 => p05 ≫ q) (Category.assoc p56 p64 p44)
      _ = (p05 ≫ p56) ≫ p64 ≫ p44 :=
        (Category.assoc p05 p56 (p64 ≫ p44)).symm
      _ = (p07 ≫ p76) ≫ p64 ≫ p44 :=
        congrArg (fun q : V0 ⟶ V6 => q ≫ p64 ≫ p44) htt
      _ = p07 ≫ p76 ≫ p64 ≫ p44 := Category.assoc p07 p76 (p64 ≫ p44)
      _ = p07 ≫ p76 ≫ p64 ≫ 𝟙 V4 :=
        congrArg (fun q : V4 ⟶ V4 => p07 ≫ p76 ≫ p64 ≫ q) hid
      _ = p07 ≫ p74 := congrArg (fun q : V7 ⟶ V4 => p07 ≫ q) hm
  exact chain.symm

end AlgebraicGeometry.Scheme.Modules
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_vertical
end ProofImplementation

end baseChangeHom_comp_vertical
