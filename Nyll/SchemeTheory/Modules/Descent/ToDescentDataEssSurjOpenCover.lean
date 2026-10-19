/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Descent.OpenCoverGluedSheaf
import Nyll.SchemeTheory.Modules.Descent.OpenCoverGluedSheafSections
import Mathlib.CategoryTheory.Sites.Descent.DescentData
/-!
# Effectivity of module descent on open covers
Restriction compatibility identifies the constructed glued sheaf with the prescribed descent datum.
-/

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar


section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover

universe v v' u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace CategoryTheory
open _root_.CategoryTheory
namespace Pseudofunctor
open _root_.CategoryTheory.Pseudofunctor
namespace LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor
open _root_.CategoryTheory

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

-- Local proof-performance refinements: Copyright (c) 2026 Naganori Yamaguchi.
-- Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
-- https://github.com/n-yamaguchi-0729
-- Transport an already proved compatibility square through an arbitrary pullback.
private theorem comm_of_pullHom {ι : Type*} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} (D₁ D₂ : F.DescentData f) {i j : ι}
    (a : D₁.obj i ⟶ D₂.obj i) (b : D₁.obj j ⟶ D₂.obj j)
    {Z₀ Z : C} (q₀ : Z₀ ⟶ S) (g₁ : Z₀ ⟶ X i) (g₂ : Z₀ ⟶ X j)
    (w₁ : g₁ ≫ f i = q₀) (w₂ : g₂ ≫ f j = q₀)
    (comm : (F.map g₁.op.toLoc).toFunctor.map a ≫ D₂.hom q₀ g₁ g₂ w₁ w₂ =
      D₁.hom q₀ g₁ g₂ w₁ w₂ ≫ (F.map g₂.op.toLoc).toFunctor.map b)
    (q : Z ⟶ S) (f₁ : Z ⟶ X i) (f₂ : Z ⟶ X j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q)
    (φ : Z ⟶ Z₀) (hφ : φ ≫ q₀ = q) (hφ₁ : φ ≫ g₁ = f₁) (hφ₂ : φ ≫ g₂ = f₂) :
    (F.map f₁.op.toLoc).toFunctor.map a ≫ D₂.hom q f₁ f₂ h₁ h₂ =
      D₁.hom q f₁ f₂ h₁ h₂ ≫ (F.map f₂.op.toLoc).toFunctor.map b := by
  rw [← D₂.pullHom_hom φ q₀ q hφ g₁ g₂ w₁ w₂ f₁ f₂ hφ₁ hφ₂,
    ← D₁.pullHom_hom φ q₀ q hφ g₁ g₂ w₁ w₂ f₁ f₂ hφ₁ hφ₂,
    map_map_eq_pullHom g₁ a φ f₁ hφ₁, map_map_eq_pullHom g₂ b φ f₂ hφ₂,
    ← pullHom_comp', ← pullHom_comp', comm]

-- Construct the comparison while the canonical object's fibers stay abstract.
private noncomputable def canonical_iso {ι : Type*} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (M : F.obj (.mk (op S))) (D : F.DescentData f)
    (e : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ D.obj i)
    (comm : ∀ ⦃Z : C⦄ (q : Z ⟶ S) ⦃i j : ι⦄ (f₁ : Z ⟶ X i) (f₂ : Z ⟶ X j)
      (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i).hom ≫ D.hom q f₁ f₂ h₁ h₂ =
        ((F.toDescentData f).obj M).hom q f₁ f₂ h₁ h₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (e j).hom) : (F.toDescentData f).obj M ≅ D :=
  Pseudofunctor.DescentData.isoMk e (fun _ q _ _ f₁ f₂ h₁ h₂ => comm q f₁ f₂ h₁ h₂)

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace ObjGlue
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Opens
variable {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)
variable (D : (MOD.{u}).DescentData (incl U))

theorem pseudo_map_map {X X' : Scheme.{u}} (f : X ⟶ X')
    {M N : X'.Modules} (ψ : M ⟶ N) {P Q : X.Modules}
    (a : P ⟶ (Modules.pullback f).obj M)
    (b : (Modules.pullback f).obj N ⟶ Q) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := X) P Q)
      (a ≫ (MOD.map f.op.toLoc).toFunctor.map ψ ≫ b)
      (a ≫ (Modules.pullback f).map ψ ≫ b) := rfl

theorem pullback_map_eq {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {M N : X'.Modules} (ψ
    : M ⟶ N) :
    (Modules.pullback f).map ψ = (restrictFunctorIsoPullback f).inv.app M ≫ (restrictFunctor
      f).map ψ ≫
      (restrictFunctorIsoPullback f).hom.app N := by
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).inv.naturality ψ, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

theorem dictM {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctorIsoPullback a').hom.app M ≫
      ((Scheme.Modules.pullbackCongr w.symm).hom.app M ≫ (Scheme.Modules.pullbackComp e a).inv.app
        M) ≫
      (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = castComp e a a' w M := by
  rw [← Mdl_mapComp'_hom_app e a M a' w]
  exact Φ_eq_congr_comp e a a' w M


theorem commZ₀_formal {X₀ X₁ X₂ S : Scheme.{u}} (p₁ : X₀ ⟶ X₁) (p₂ : X₀ ⟶ X₂) (ι₁ : X₁ ⟶ S) (ι₂ :
    X₂ ⟶ S)
    (q₀ : X₀ ⟶ S) [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion ι₁] [IsOpenImmersion
      ι₂]
    [IsOpenImmersion q₀] (w₁ : p₁ ≫ ι₁ = q₀) (w₂ : p₂ ≫ ι₂ = q₀) (G : S.Modules) (M₁ : X₁.Modules)
    (M₂ : X₂.Modules) (r₁ : (restrictFunctor ι₁).obj G ⟶ M₁) (r₂ : (restrictFunctor ι₂).obj G ⟶ M₂)
    (ρ₀ : (restrictFunctor p₁).obj M₁ ⟶ (restrictFunctor p₂).obj M₂)
    (φ₀ : (Modules.pullback p₁).obj M₁ ⟶ (Modules.pullback p₂).obj M₂)
    (hφ₀ : (restrictFunctorIsoPullback p₁).hom.app M₁ ≫ φ₀ ≫ (restrictFunctorIsoPullback
      p₂).inv.app M₂ = ρ₀)
    (cs : castComp p₁ ι₁ q₀ w₁ G ≫ (restrictFunctor p₁).map r₁ ≫ ρ₀ =
      castComp p₂ ι₂ q₀ w₂ G ≫ (restrictFunctor p₂).map r₂) :
    (Modules.pullback p₁).map ((restrictFunctorIsoPullback ι₁).inv.app G ≫ r₁) ≫ φ₀ =
      (((Scheme.Modules.pullbackComp p₁ ι₁).hom.app G ≫ (Scheme.Modules.pullbackCongr w₁).hom.app
        G) ≫
        (Scheme.Modules.pullbackCongr w₂.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₂
          ι₂).inv.app G) ≫
      (Modules.pullback p₂).map ((restrictFunctorIsoPullback ι₂).inv.app G ≫ r₂) := by
  rw [← hφ₀, ← dictM p₁ ι₁ q₀ w₁ G, ← dictM p₂ ι₂ q₀ w₂ G] at cs
  have c0 : (Scheme.Modules.pullbackComp p₁ ι₁).inv.app G ≫ (Scheme.Modules.pullbackComp p₁
    ι₁).hom.app G = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  refine (cancel_epi ((restrictFunctorIsoPullback q₀).hom.app G ≫
      ((Scheme.Modules.pullbackCongr w₁.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₁
        ι₁).inv.app G))).mp ?_
  refine (cancel_mono ((restrictFunctorIsoPullback p₂).inv.app M₂)).mp ?_
  simp only [Functor.comp_obj, Functor.map_comp, pullback_map_eq, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id, Scheme.Modules.pullbackCongr, eqToIso.hom,
    eqToHom_app, eqToHom_trans_assoc, reassoc_of% c0] at cs ⊢
  exact cs

theorem gluedIso_hom (k : ι) : (gluedIso U D k).hom =
    (restrictFunctorIsoPullback (incl U k)).inv.app (glued U D) ≫ restrictGluedHom U D k := rfl

-- Transport the restriction square before specializing its schemes to covering opens.
private theorem comm_of_restriction_square {κ : Type u} {S Z : Scheme.{u}}
    {X : κ → Scheme.{u}} (f : ∀ k, X k ⟶ S) (E : MOD.DescentData f)
    (i j : κ) (q : Z ⟶ S) (a : Z ⟶ X i) (b : Z ⟶ X j)
    [IsOpenImmersion q] [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion (f i)] [IsOpenImmersion (f j)]
    (wa : a ≫ f i = q) (wb : b ≫ f j = q) (G : S.Modules)
    (ei : (Modules.pullback (f i)).obj G ≅ E.obj i)
    (ej : (Modules.pullback (f j)).obj G ≅ E.obj j)
    (ri : (restrictFunctor (f i)).obj G ⟶ E.obj i)
    (rj : (restrictFunctor (f j)).obj G ⟶ E.obj j)
    (hei : ei.hom = (restrictFunctorIsoPullback (f i)).inv.app G ≫ ri)
    (hej : ej.hom = (restrictFunctorIsoPullback (f j)).inv.app G ≫ rj)
    (rho : (restrictFunctor a).obj (E.obj i) ⟶ (restrictFunctor b).obj (E.obj j))
    (htrans : (restrictFunctorIsoPullback a).hom.app (E.obj i) ≫
      E.hom q a b wa wb ≫ (restrictFunctorIsoPullback b).inv.app (E.obj j) = rho)
    (cs : castComp a (f i) q wa G ≫ (restrictFunctor a).map ri ≫ rho =
      castComp b (f j) q wb G ≫ (restrictFunctor b).map rj) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ E.hom q a b wa wb)
      (((MOD.toDescentData f).obj G).hom q a b wa wb ≫
        (MOD.map b.op.toLoc).toFunctor.map ej.hom) := by
  let transition : (Modules.pullback a).obj (E.obj i) ⟶
      (Modules.pullback b).obj (E.obj j) := E.hom q a b wa wb
  let canonical : (Modules.pullback a).obj ((Modules.pullback (f i)).obj G) ⟶
      (Modules.pullback b).obj ((Modules.pullback (f j)).obj G) :=
    ((Scheme.Modules.pullbackComp a (f i)).hom.app G ≫
        (Scheme.Modules.pullbackCongr wa).hom.app G) ≫
      (Scheme.Modules.pullbackCongr wb.symm).hom.app G ≫
      (Scheme.Modules.pullbackComp b (f j)).inv.app G
  have hMap₁ : @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ transition)
      ((Modules.pullback a).map ei.hom ≫ transition) := by
    exact (Category.id_comp (obj := Z.Modules)
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ transition)).symm.trans
      ((pseudo_map_map a ei.hom (𝟙 _) transition).trans
        (Category.id_comp (obj := Z.Modules)
          ((Modules.pullback a).map ei.hom ≫ transition)))
  have hMap₂ : @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      (canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom)
      (canonical ≫ (Modules.pullback b).map ej.hom) := by
    exact ((Category.assoc (obj := Z.Modules)
      canonical ((MOD.map b.op.toLoc).toFunctor.map ej.hom) (𝟙 _)).symm.trans
        (Category.comp_id (obj := Z.Modules)
          (canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom))).symm.trans
      ((pseudo_map_map b ej.hom canonical (𝟙 _)).trans
        ((Category.assoc (obj := Z.Modules)
          canonical ((Modules.pullback b).map ej.hom) (𝟙 _)).symm.trans
          (Category.comp_id (obj := Z.Modules)
            (canonical ≫ (Modules.pullback b).map ej.hom))))
  have hFormal : (Modules.pullback a).map ei.hom ≫ transition =
      canonical ≫ (Modules.pullback b).map ej.hom := by
    rw [hei, hej]
    exact commZ₀_formal a b (f i) (f j) q wa wb G
      (E.obj i) (E.obj j) ri rj rho transition htrans cs
  have hCanonical : ((MOD.toDescentData f).obj G).hom q a b wa wb ≫
      (MOD.map b.op.toLoc).toFunctor.map ej.hom =
      canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom := by
    dsimp only [canonical]
    rw [← Mdl_mapComp'_inv_app a (f i) G q wa,
      ← Mdl_mapComp'_hom_app b (f j) G q wb]
    rfl
  exact hMap₁.trans (hFormal.trans (hCanonical.trans hMap₂).symm)

theorem commZ₀ (i j : ι) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom
      (X := ((U i ⊓ U j : Y.Opens) : Scheme.{u}))
      ((Modules.pullback (p₁ U i j)).obj
        ((Modules.pullback (incl U i)).obj (glued U D)))
      ((Modules.pullback (p₂ U i j)).obj (Dobj U D j)))
      ((MOD.map (p₁ U i j).op.toLoc).toFunctor.map (gluedIso U D i).hom ≫
        D.hom (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j)
          (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right))
      (((MOD.toDescentData (incl U)).obj (glued U D)).hom
          (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j)
          (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right) ≫
        (MOD.map (p₂ U i j).op.toLoc).toFunctor.map (gluedIso U D j).hom) := by
  exact comm_of_restriction_square (incl U) D i j (U i ⊓ U j).ι
    (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)
    (glued U D) (gluedIso U D i) (gluedIso U D j)
    (restrictGluedHom U D i) (restrictGluedHom U D j)
    (gluedIso_hom U D i) (gluedIso_hom U D j) (ρ U D i j).hom
    (τ_hom_eq U D i j (U i ⊓ U j) inf_le_left inf_le_right).symm
    (comm_sections U D i j)

theorem gluedIso_comm ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z
    ⟶ (U j : Scheme.{u}))
    (h₁ : f₁ ≫ incl U i = q) (h₂ : f₂ ≫ incl U j = q) :
    (MOD.map f₁.op.toLoc).toFunctor.map (gluedIso U D i).hom ≫ D.hom q f₁ f₂ h₁ h₂ =
      ((MOD.toDescentData (incl U)).obj (glued U D)).hom q f₁ f₂ h₁ h₂ ≫
        (MOD.map f₂.op.toLoc).toFunctor.map (gluedIso U D j).hom := by
  have H : Set.range q.base ⊆ Set.range (U i ⊓ U j).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← h₁, ← Scheme.Opens.range_ι (U i)]
      exact ⟨f₁.base z, rfl⟩
    · rw [← h₂, ← Scheme.Opens.range_ι (U j)]
      exact ⟨f₂.base z, rfl⟩
  let φ := IsOpenImmersion.lift (U i ⊓ U j).ι q H
  have hφ : φ ≫ (U i ⊓ U j).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hφ₁ : φ ≫ p₁ U i j = f₁ := by
    rw [← cancel_mono (U i).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₁.symm
  have hφ₂ : φ ≫ p₂ U i j = f₂ := by
    rw [← cancel_mono (U j).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₂.symm
  exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.comm_of_pullHom
    ((MOD.toDescentData (incl U)).obj (glued U D)) D (gluedIso U D i).hom (gluedIso U D j).hom
    (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)
    (commZ₀ U D i j) q f₁ f₂ h₁ h₂ φ hφ hφ₁ hφ₂

/-- The descent-data isomorphism between the glued sheaf and the prescribed datum. -/
noncomputable def isoDescentData : (MOD.toDescentData (incl U)).obj (glued U D) ≅ D :=
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.canonical_iso (F := MOD)
    (incl U) (glued U D) D (fun k => gluedIso U D k)
    (fun _Z q _i _j f₁ f₂ h₁ h₂ => gluedIso_comm U D q f₁ f₂ h₁ h₂)

theorem essSurj_incl : (MOD.toDescentData (incl U)).EssSurj :=
  ⟨fun D => ⟨glued U D, ⟨isoDescentData U D⟩⟩⟩

end Opens

theorem toDescentData_essSurj_of_openCover'
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g
      i)]
    (_hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (MOD.toDescentData g).EssSurj :=
  (essSurj_iff_of_sieve_eq g (fun O : Ranges g => O.1.ι) (sieve_ofArrows_eq_opensRange g)).mpr
    (essSurj_incl (fun O : Ranges g => O.1))

end AlgebraicGeometry.Scheme.Modules.ObjGlue

open _root_.AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g
      i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).EssSurj :=
  AlgebraicGeometry.Scheme.Modules.ObjGlue.toDescentData_essSurj_of_openCover' g hg
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover
end ProofImplementation
