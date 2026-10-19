/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesTildePullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Affine pullback and associated module sheaves

Compares pullback of an associated module sheaf with extension of scalars.
-/

section TildePullback

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)


/-- Global sections of pushforward along Spec.map agree with restriction of scalars. -/
def Scheme.Modules.pushforwardSpecCompΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N =>
      have nativeIso {T : Type u} [CommRing T] (L P : ModuleCat.{u} T)
          (e : L ≃ₗ[T] P) : L ≅ P := LinearEquiv.toModuleIso e
      nativeIso
      ((Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj N)
      ((moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj N)
      { __ := AddEquiv.refl _
        map_smul' := fun r m => by
          change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom).obj _ at m
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
          have h1 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of R)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          have h2 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of S)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          simp only [h1, h2, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
          have key := congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ.hom r)
            (Scheme.ΓSpecIso_inv_naturality φ)
          have hcoeff : (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) =
              (Scheme.ΓSpecIso S).inv.hom (φ.hom r) := key.symm
          exact congrArg (fun a : Γ(Spec S, ⊤) => a • (show Γ(N, ⊤) from m)) hcoeff })
    (fun f => by ext; rfl)

/-- The natural comparison between pulling back an associated module sheaf and extending scalars. -/
def tilde.functorCompPullbackSpecIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecCompΓIso φ).symm)

/-- The comparison between the pullback of an associated module sheaf and the sheaf of the
  scalar extension. -/
def tilde.pullbackSpecIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tilde.functorCompPullbackSpecIso φ).app M

@[simp] theorem tilde.functorCompPullbackSpecIso_app (M : ModuleCat.{u} R) :
    (tilde.functorCompPullbackSpecIso φ).app M = tilde.pullbackSpecIso φ M := rfl

theorem tilde.pullbackSpecIso_hom_naturality {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor R).map f) ≫
        (tilde.pullbackSpecIso φ M').hom =
      (tilde.pullbackSpecIso φ M).hom ≫ (tilde.functor S).map ((ModuleCat.extendScalars
        φ.hom).map f) :=
  (tilde.functorCompPullbackSpecIso φ).hom.naturality f

end AlgebraicGeometry

end

end TildePullback

section tilde_pullbackSpecIso_unit

/-!
# Compatibility of affine pullback with adjunction units

Relates the affine pullback comparison isomorphism to the unit of the pullback adjunction.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_unit

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem _root_.AlgebraicGeometry.tilde.pullbackSpecIso_unit {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars
        φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h2
  exact h2

end AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_unit
end ProofImplementation

end tilde_pullbackSpecIso_unit

section tilde_pullbackSpecIso_hom_app_top_unit_toOpen

/-!
# Pullback of sections represented by module elements

The affine pullback comparison sends a module element represented as a section
to the section represented by its scalar extension.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_hom_app_top_unit_toOpen

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace tilde
open _root_.AlgebraicGeometry.tilde
end AlgebraicGeometry.tilde
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.tilde in
theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux {R S : CommRingCat.{u}} (φ : R ⟶ S) (M :
  ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj
          M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h2
  exact h2

theorem _root_.AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen {R S :
  CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by
  have h := congrArg (fun ψ => ψ.hom m) (AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux φ M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Adjunction.comp_unit_app] at h
  exact h

end AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_hom_app_top_unit_toOpen
end ProofImplementation

end tilde_pullbackSpecIso_hom_app_top_unit_toOpen

section tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom

/-!
# tilde pullback map pullback Spec Iso hom comp pullback Spec Iso hom
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom


universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace TildePullbackCompAux
open _root_.AlgebraicGeometry

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {X : Type u₄} {Y : Type u₅} {Z : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} X] [Category.{v₅} Y] [Category.{v₆} Z]
  {FR : A ⥤ X} {GR : X ⥤ A} {FS : B ⥤ Y} {GS : Y ⥤ B} {FT : C ⥤ Z} {GT : Z ⥤ C}
  (tR : FR ⊣ GR) (tS : FS ⊣ GS) (tT : FT ⊣ GT)
  {Eφ : A ⥤ B} {Rφ : B ⥤ A} {Eψ : B ⥤ C} {Rψ : C ⥤ B} {Eφψ : A ⥤ C} {Rφψ : C ⥤ A}
  (eφ : Eφ ⊣ Rφ) (eψ : Eψ ⊣ Rψ) (eφψ : Eφψ ⊣ Rφψ)
  {Pφ : X ⥤ Y} {Qφ : Y ⥤ X} {Pψ : Y ⥤ Z} {Qψ : Z ⥤ Y} {Pφψ : X ⥤ Z} {Qφψ : Z ⥤ X}
  (pφ : Pφ ⊣ Qφ) (pψ : Pψ ⊣ Qψ) (pφψ : Pφψ ⊣ Qφψ)
  (dφ : Qφ ⋙ GR ≅ GS ⋙ Rφ) (dψ : Qψ ⋙ GS ≅ GT ⋙ Rψ) (dφψ : Qφψ ⋙ GR ≅ GT ⋙ Rφψ)
  (q : Qφψ ⟶ Qψ ⋙ Qφ) (r : Rφψ ⟶ Rψ ⋙ Rφ)
  (M : A)
  (βφ : Pφ.obj (FR.obj M) ⟶ FS.obj (Eφ.obj M))
  (βψ : Pψ.obj (FS.obj (Eφ.obj M)) ⟶ FT.obj (Eψ.obj (Eφ.obj M)))
  (βφψ : Pφψ.obj (FR.obj M) ⟶ FT.obj (Eφψ.obj M))
  (κ : (Pφ ⋙ Pψ).obj (FR.obj M) ⟶ Pφψ.obj (FR.obj M))
  (ε : Eφψ.obj M ⟶ (Eφ ⋙ Eψ).obj M)

theorem main
    (hφ : (tR.comp pφ).unit.app M ≫ (Qφ ⋙ GR).map βφ ≫ dφ.hom.app _ =
      eφ.unit.app M ≫ Rφ.map (tS.unit.app _))
    (hψ : (tS.comp pψ).unit.app (Eφ.obj M) ≫ (Qψ ⋙ GS).map βψ ≫ dψ.hom.app _ =
      eψ.unit.app _ ≫ Rψ.map (tT.unit.app _))
    (hφψ : (tR.comp pφψ).unit.app M ≫ (Qφψ ⋙ GR).map βφψ ≫ dφψ.hom.app _ =
      eφψ.unit.app M ≫ Rφψ.map (tT.unit.app _))
    (hκ : (pφ.comp pψ).unit.app (FR.obj M) ≫ (Qψ ⋙ Qφ).map κ = pφψ.unit.app _ ≫ q.app _)
    (hε : eφψ.unit.app M ≫ Rφψ.map ε ≫ r.app _ = eφ.unit.app M ≫ Rφ.map (eψ.unit.app _))
    (hcoh : ∀ N : Z, GR.map (q.app N) ≫ dφ.hom.app (Qψ.obj N) ≫ Rφ.map (dψ.hom.app N) =
      dφψ.hom.app N ≫ r.app (GT.obj N)) :
    Pψ.map βφ ≫ βψ = κ ≫ βφψ ≫ FT.map ε := by
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Adjunction.comp_unit_app,
    Category.assoc] at hφ hψ hφψ hκ hε hcoh
  have inj : Function.Injective (fun f : Pψ.obj (Pφ.obj (FR.obj M)) ⟶ FT.obj (Eψ.obj (Eφ.obj M)) =>
      tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map f)) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M))))) := by
    intro f g h
    dsimp only at h
    let N := FT.obj (Eψ.obj (Eφ.obj M))
    have h2 : (tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
          GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map f))) ≫
          (dφ.app (Qψ.obj N) ≪≫ Rφ.mapIso (dψ.app N)).hom =
        (tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
          GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map g))) ≫
          (dφ.app (Qψ.obj N) ≪≫ Rφ.mapIso (dψ.app N)).hom := by
      simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h
    rw [Iso.cancel_iso_hom_right] at h2
    apply (((tR.comp pφ).comp pψ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Adjunction.comp_unit_app, Functor.comp_map,
      Functor.comp_obj, Category.assoc]
    exact h2
  apply inj
  dsimp only
  have lhs : tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map (Pψ.map βφ ≫
          βψ))) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M)))) =
      eφ.unit.app M ≫ Rφ.map (eψ.unit.app (Eφ.obj M)) ≫
        Rφ.map (Rψ.map (tT.unit.app (Eψ.obj (Eφ.obj M)))) := by
    have n1 := congr_arg (fun t => GR.map (Qφ.map t)) (pψ.unit_naturality βφ)
    simp only [Functor.map_comp] at n1
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    rw [reassoc_of% n1]
    have n2 := dφ.hom.naturality (pψ.unit.app (FS.obj (Eφ.obj M)) ≫ Qψ.map βψ)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.map_comp,
      Category.assoc] at n2
    rw [reassoc_of% n2, reassoc_of% hφ]
    simp only [← Functor.map_comp, hψ]
  have rhs : tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫
        GR.map (Qφ.map (Qψ.map (κ ≫ βφψ ≫ FT.map ε))) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M)))) =
      eφ.unit.app M ≫ Rφ.map (eψ.unit.app (Eφ.obj M)) ≫
        Rφ.map (Rψ.map (tT.unit.app (Eψ.obj (Eφ.obj M)))) := by
    have k1 := congr_arg (fun t => GR.map t) hκ
    simp only [Functor.map_comp] at k1
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    rw [reassoc_of% k1]
    have k2 := congr_arg (fun t => GR.map t) (q.naturality (βφψ ≫ FT.map ε)).symm
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at k2
    rw [reassoc_of% k2, hcoh]
    have k3 := dφψ.hom.naturality (FT.map ε)
    simp only [Functor.comp_obj, Functor.comp_map] at k3
    rw [reassoc_of% k3, reassoc_of% hφψ]
    have k4 := congr_arg (fun t => Rφψ.map t) (tT.unit_naturality ε)
    simp only [Functor.comp_obj, Functor.map_comp] at k4
    rw [reassoc_of% k4]
    have k5 := r.naturality (tT.unit.app (Eψ.obj (Eφ.obj M)))
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at k5
    rw [k5, reassoc_of% hε]
  exact lhs.trans rhs.symm

end AlgebraicGeometry.TildePullbackCompAux

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace TildePullbackCompAux
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

section Generic

variable {X Y Z : Scheme.{u}}

theorem pushforwardCongr_rfl (f : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  ext N U x
  simp [Scheme.Modules.pushforwardCongr_hom_app_app]

theorem comp_unit_app_comp_map_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.Modules) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app A ≫
        (pushforward f ⋙ pushforward g).map ((pullbackComp f g).hom.app A) =
      (pullbackPushforwardAdjunction (f ≫ g)).unit.app A ≫ (pushforwardComp f g).inv.app _ := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)) (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f
      g).inv A
  rw [conjugateEquiv_pullbackComp_inv] at h
  refine (Iso.eq_comp_inv ((pushforwardComp f g).app _)).mpr ?_
  rw [Iso.app_hom, Category.assoc]
  erw [(pushforwardComp f g).hom.naturality ((pullbackComp f g).hom.app A)]
  erw [reassoc_of% h]
  erw [← (pushforward (f ≫ g)).map_comp, Iso.inv_hom_id_app]
  rw [(pushforward (f ≫ g)).map_id, Category.comp_id]

theorem comp_unit_app_comp_map_pullbackComp_pullbackCongr (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    (h : f ≫ g = k) (A : Z.Modules) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app A ≫
        (pushforward f ⋙ pushforward g).map ((pullbackComp f g).hom.app A ≫ (pullbackCongr
          h).hom.app A) =
      (pullbackPushforwardAdjunction k).unit.app A ≫
        ((pushforwardCongr h).inv ≫ (pushforwardComp f g).inv).app ((pullback k).obj A) := by
  subst h
  simp only [Functor.map_comp, pushforwardCongr_rfl, Iso.refl_inv, Category.id_comp]
  rw [← comp_unit_app_comp_map_pullbackComp]
  simp [Scheme.Modules.pullbackCongr]

variable {R : CommRingCat.{u}}

theorem moduleSpecΓFunctor_map_pushforwardCongr_inv_apply {f g : X ⟶ Spec R} (hf : f = g)
    (N : X.Modules) (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward g).obj N)) :
    ((moduleSpecΓFunctor (R := R)).map ((pushforwardCongr hf).inv.app N)).hom y = y := by
  subst hf
  simp [pushforwardCongr_rfl]

theorem pushforwardSpecCompΓIso_hom_app_apply {S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec
  S).Modules)
    (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj N)) :
    ((pushforwardSpecCompΓIso φ).hom.app N :
      (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj N) ⟶
        (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)).hom y = y :=
          rfl

end Generic

section Concrete

variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T)

theorem hε (M : ModuleCat.{u} R) :
    (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom).unit.app M ≫
        (ModuleCat.restrictScalars (φ ≫ ψ).hom).map ((ModuleCat.extendScalarsComp φ.hom
          ψ.hom).hom.app M) ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.extendScalars φ.hom).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
        (ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
          ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h := ModuleCat.homEquiv_extendScalarsComp φ.hom ψ.hom M
  rw [Adjunction.homEquiv_unit] at h
  exact (Iso.eq_comp_inv ((ModuleCat.restrictScalarsComp φ.hom ψ.hom).app _)
    (f := (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
        ((ModuleCat.extendScalars φ.hom).obj M)))
    (g := (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom).unit.app M ≫
      (ModuleCat.restrictScalars (φ ≫ ψ).hom).map
        ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M))).mp h

theorem tail3_apply (N : (Spec T).Modules)
    (z : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map ψ ≫ Spec.map φ)).obj N)) :
    ((ModuleCat.restrictScalars φ.hom).map ((pushforwardSpecCompΓIso ψ).hom.app N)).hom
      (((pushforwardSpecCompΓIso φ).hom.app ((pushforward (Spec.map ψ)).obj N)).hom
        (((moduleSpecΓFunctor (R := R)).map ((pushforwardComp (Spec.map ψ) (Spec.map φ)).inv.app
          N)).hom z)) =
      z := rfl

theorem rhs_apply (N : (Spec T).Modules)
    (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map (φ ≫ ψ))).obj N)) :
    ((pushforwardSpecCompΓIso (φ ≫ ψ)).hom.app N ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app ((moduleSpecΓFunctor (R := T)).obj
        N)).hom y = y := rfl

theorem hcoh (N : (Spec T).Modules) :
    (moduleSpecΓFunctor (R := R)).map
        (((pushforwardCongr (Spec.map_comp φ ψ).symm).inv ≫
            (pushforwardComp (Spec.map ψ) (Spec.map φ)).inv).app N) ≫
      (pushforwardSpecCompΓIso φ).hom.app ((pushforward (Spec.map ψ)).obj N) ≫
      (ModuleCat.restrictScalars φ.hom).map ((pushforwardSpecCompΓIso ψ).hom.app N) =
    (pushforwardSpecCompΓIso (φ ≫ ψ)).hom.app N ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app ((moduleSpecΓFunctor (R := T)).obj N) :=
        by
  ext y
  refine Eq.trans ?_ (rhs_apply φ ψ N y).symm
  simp only [NatTrans.comp_app, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  refine (tail3_apply φ ψ N _).trans ?_
  exact moduleSpecΓFunctor_map_pushforwardCongr_inv_apply _ N y

end Concrete

end AlgebraicGeometry.TildePullbackCompAux

open AlgebraicGeometry.TildePullbackCompAux _root_.AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
    {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map ψ)).map (tilde.pullbackSpecIso φ M).hom ≫
        (tilde.pullbackSpecIso ψ ((ModuleCat.extendScalars φ.hom).obj M)).hom =
      (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).hom.app (tilde M) ≫
        (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).hom.app (tilde M) ≫
        (tilde.pullbackSpecIso (φ ≫ ψ) M).hom ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  have := main (@id (@Adjunction (ModuleCat R) _ (Spec R).Modules (Scheme.Modules.instCategory :
    Category (Spec R).Modules)
      (tilde.functor R) moduleSpecΓFunctor) (tilde.adjunction (R := R)))
    (@id (@Adjunction (ModuleCat S) _ (Spec S).Modules (Scheme.Modules.instCategory : Category
      (Spec S).Modules)
      (tilde.functor S) moduleSpecΓFunctor) (tilde.adjunction (R := S)))
    (@id (@Adjunction (ModuleCat T) _ (Spec T).Modules (Scheme.Modules.instCategory : Category
      (Spec T).Modules)
      (tilde.functor T) moduleSpecΓFunctor) (tilde.adjunction (R := T)))
    (ModuleCat.extendRestrictScalarsAdj φ.hom) (ModuleCat.extendRestrictScalarsAdj ψ.hom)
    (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom)
    (pullbackPushforwardAdjunction (Spec.map φ)) (pullbackPushforwardAdjunction (Spec.map ψ))
    (pullbackPushforwardAdjunction (Spec.map (φ ≫ ψ)))
    (pushforwardSpecCompΓIso φ) (pushforwardSpecCompΓIso ψ) (pushforwardSpecCompΓIso (φ ≫ ψ))
    ((pushforwardCongr (Spec.map_comp φ ψ).symm).inv ≫ (pushforwardComp (Spec.map ψ) (Spec.map
      φ)).inv)
    (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom
    M (tilde.pullbackSpecIso φ M).hom (tilde.pullbackSpecIso ψ ((ModuleCat.extendScalars φ.hom).obj
      M)).hom
    (tilde.pullbackSpecIso (φ ≫ ψ) M).hom
    _ ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M)
    (tilde.pullbackSpecIso_unit φ M) (tilde.pullbackSpecIso_unit ψ _) (tilde.pullbackSpecIso_unit
      (φ ≫ ψ) M)
    (comp_unit_app_comp_map_pullbackComp_pullbackCongr (Spec.map ψ) (Spec.map φ) (Spec.map_comp φ
      ψ).symm (tilde M))
    (hε φ ψ M) (hcoh φ ψ)
  exact this.trans (@Category.assoc _ _
    ((Scheme.Modules.pullback (Spec.map φ) ⋙ Scheme.Modules.pullback (Spec.map ψ)).obj (tilde M)) _
    ((Scheme.Modules.pullback (Spec.map (φ ≫ ψ))).obj (tilde M)) _ _ _ _)
end tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
