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
/-!
# Local sections and restriction isomorphisms for the glued module sheaf
The compatible-family construction is preserved, together with its original descent data.
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

theorem preimage_ι_eq_incO (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    O.ι ⁻¹ᵁ V = (incO U i O hi) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem T_le_in (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) ≤ (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi]; exact Scheme.Hom.image_preimage_le _ _

theorem T_eq (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) = (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  exact fun y hy => hV hy

theorem T_le_out (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (U i).ι ⁻¹ᵁ V ≤ (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) :=
  (T_eq U i O hi V hV).symm.le

/-- Transport a section between two covering modules through a smaller common open. -/
noncomputable def T (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : Γ(Dobj U D j, (U j).ι ⁻¹ᵁ V) :=
  (Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
    ((τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))

theorem T_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : T U D i i O hi hi V hV x = x := by
  simp only [T, τ_self, Scheme.Modules.Hom.id_app]
  exact map_map_self _ _ _ x

theorem T_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) (V :
    Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D j k O hj hk V hV (T U D i j O hi hj V hV x) = T U D i k O hi hk V hV x := by
  let aij : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
  let ajk : (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D k).presheaf.obj (op ((incO U k O hk) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D j k O hj hk).hom.app (O.ι ⁻¹ᵁ V)
  let aik : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D k).presheaf.obj (op ((incO U k O hk) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i k O hi hk).hom.app (O.ι ⁻¹ᵁ V)
  have hc : aij ≫ ajk = aik :=
    (Scheme.Modules.Hom.comp_app (τ U D i j O hi hj).hom
      (τ U D j k O hj hk).hom (U := O.ι ⁻¹ᵁ V)).symm.trans
      (congrArg
        (fun a : (Dobj U D i).restrict (incO U i O hi) ⟶
            (Dobj U D k).restrict (incO U k O hk) => a.app (O.ι ⁻¹ᵁ V))
        (τ_comp U D i j k O hi hj hk))
  change (Dobj U D k).presheaf.map (homOfLE (T_le_out U k O hk V hV)).op
      (ajk ((Dobj U D j).presheaf.map (homOfLE (T_le_in U j O hj V)).op
        ((Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
          (aij ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))))) =
    (Dobj U D k).presheaf.map (homOfLE (T_le_out U k O hk V hV)).op
      (aik ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))
  rw [map_map_self]
  rw [← hc]
  rfl

theorem T_res (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) {V V' : Y.Opens} (hV : V ≤ O)
    (hV' : V' ≤ V)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V' (hV'.trans hV) ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono
      hV')).op x) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op (T U D i j O hi hj V hV
        x) := by
  let aV : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
  let aV' : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V'))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V'))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V')
  change (Dobj U D j).presheaf.map
      (homOfLE (T_le_out U j O hj V' (hV'.trans hV))).op
      (aV' ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V')).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV')).op x))) =
    (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op
      ((Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
        (aV ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)))
  rw [map_map, map_map]
  have nat : aV' ((Dobj U D i).presheaf.map
      ((Hom.opensFunctor (incO U i O hi)).map (homOfLE (O.ι.preimage_mono hV'))).op
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)) =
      (Dobj U D j).presheaf.map
        ((Hom.opensFunctor (incO U j O hj)).map (homOfLE (O.ι.preimage_mono hV'))).op
        (aV ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)) :=
    app_presheaf_map (τ U D i j O hi hj).hom (homOfLE (O.ι.preimage_mono hV'))
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  have step1 : (Dobj U D i).presheaf.map
      (homOfLE (T_le_in U i O hi V') ≫ homOfLE ((U i).ι.preimage_mono hV')).op x =
      (Dobj U D i).presheaf.map
        ((Hom.opensFunctor (incO U i O hi)).map (homOfLE (O.ι.preimage_mono hV'))).op
        ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x) := by
    rw [map_map]
    exact presheaf_map_congr _ _ _ _
  rw [step1, nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

/-- The canonical comparison between restriction along a composite and iterated restriction. -/
noncomputable def Φ {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorIsoPullback a').hom.app M ≫
    (MOD.mapComp' a.op.toLoc e.op.toLoc a'.op.toLoc (by rw [← w]; rfl)).hom.toNatTrans.app M ≫
    (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) ≫
    (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M)

theorem Φ_eq_congr_comp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    Φ e a a' w M = (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M
      := by
  subst w
  have hc : (restrictFunctorCongr (rfl : e ≫ a = e ≫ a)).hom.app M = 𝟙 _ := by
    apply Scheme.Modules.hom_ext; intro V
    erw [restrictFunctorCongr_hom_app_app]
    rw [eqToHom_refl, op_id, M.presheaf.map_id]
    rfl
  rw [hc, Category.id_comp, Φ]
  erw [restrictFunctorIsoPullback_comp_hom_app e a M, mapComp'_hom_app_eq e a M (e ≫ a) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp,
    Category.assoc]
  have c1 : (restrictFunctorIsoPullback e).hom.app ((Modules.pullback a).obj M) ≫
      (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) = 𝟙 _ :=
        Iso.hom_inv_id_app _ _
  have c2 : (restrictFunctor e).map ((restrictFunctorIsoPullback a).hom.app M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have c0 : (pullbackComp e a).hom.app M ≫ (pullbackComp e a).inv.app M = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  erw [reassoc_of% c0, reassoc_of% c1, c2]
  erw [Category.comp_id]

theorem image_comp_of_eq {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (V : X₀.Opens) : a ''ᵁ (e ''ᵁ V) =
      a' ''ᵁ V := by
  subst w
  apply TopologicalSpace.Opens.ext
  exact (Set.image_comp _ _ _).symm

theorem Φ_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (Φ e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h1 := restrictFunctorCongr_hom_app_app (U := V) w.symm M
  have h2 := restrictFunctorComp_hom_app_app (U := V) e a M
  rw [Φ_eq_congr_comp]
  refine (show _ = (Hom.app ((restrictFunctorComp e a).hom.app M) V)
    ((Hom.app ((restrictFunctorCongr w.symm).hom.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

/-- The forward comparison from a composite restriction to its iterated restriction. -/
noncomputable def castComp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M

/-- The reverse comparison from an iterated restriction to its composite restriction. -/
noncomputable def castComp' {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor e).obj ((restrictFunctor a).obj M) ⟶ (restrictFunctor a').obj M :=
  (restrictFunctorComp e a).inv.app M ≫ (restrictFunctorCongr w).hom.app M

theorem castComp_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (castComp e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h := Φ_app e a a' w M V x
  rw [Φ_eq_congr_comp] at h
  exact h

theorem castComp'_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a ''ᵁ (e ''ᵁ V))) :
    (castComp' e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w
      V).symm).op x :
      Γ(M, a' ''ᵁ V)) := by
  have h1 := restrictFunctorComp_inv_app_app (U := V) e a M
  have h2 := restrictFunctorCongr_hom_app_app (U := V) w M
  refine (show _ = (Hom.app ((restrictFunctorCongr w).hom.app M) V)
    ((Hom.app ((restrictFunctorComp e a).inv.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem τ_hom_eq (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) : (τ U D i j O hi hj).hom =
    (restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
      D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
      (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j) := by
  let ei : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let ej : (Dobj U D j).restrict (incO U j O hj) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    (restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)
  let d : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj)
  have hd : d.hom = (D.hom O.ι (incO U i O hi) (incO U j O hj)
      (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) :
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ⟶
        (Modules.pullback (incO U j O hj)).obj (Dobj U D j)) := rfl
  exact congrArg
    (fun a : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ⟶
        (Modules.pullback (incO U j O hj)).obj (Dobj U D j) =>
      ei.hom ≫ a ≫ ej.inv) hd

theorem τ_locality (i j : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) (hj : O ≤ U j) :
    (restrictFunctorIsoPullback (incO U i O' (hO'.trans hi))).hom.app (D.obj i) ≫
      D.hom O'.ι (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
        (Y.homOfLE_ι (hO'.trans hi)) (Y.homOfLE_ι (hO'.trans hj)) ≫
      (restrictFunctorIsoPullback (incO U j O' (hO'.trans hj))).inv.app (D.obj j) =
    (restrictFunctorCongr (incO_comp U i hO' hi).symm).hom.app (D.obj i) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U i O hi)).hom.app (D.obj i) ≫
      (restrictFunctor (Y.homOfLE hO')).map
        ((restrictFunctorIsoPullback (incO U i O hi)).hom.app (D.obj i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (D.obj j)) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U j O hj)).inv.app (D.obj j) ≫
      (restrictFunctorCongr (incO_comp U j hO' hj)).hom.app (D.obj j) := by
  have hh := crux_MOD (Y.homOfLE hO') (incO U i O hi) (incO U j O hj)
    (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj)) (incO_comp U i hO' hi) (incO_comp U
      j hO' hj)
    (D.obj i) (D.obj j) (D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι
      hj))
  rw [D_pullHom U D (Y.homOfLE hO') O.ι O'.ι (Y.homOfLE_ι hO') (incO U i O hi) (incO U j O hj)
    (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
    (incO_comp U i hO' hi) (incO_comp U j hO' hj) (Y.homOfLE_ι _) (Y.homOfLE_ι _)] at hh
  exact hh

theorem T_indep (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V hV x = T U D i j V (hV.trans hi) (hV.trans hj) V le_rfl x := by
  symm
  simp only [T]
  have loc := τ_locality U D i j hV hi hj
  have hsub : (Y.homOfLE hV) ''ᵁ (V.ι ⁻¹ᵁ V) ≤ O.ι ⁻¹ᵁ V :=
    ((Y.homOfLE hV).image_le_opensRange _).trans (by rw [Scheme.opensRange_homOfLE])
  have ev : ∀ y, (τ U D i j V (hV.trans hi) (hV.trans hj)).hom.app (V.ι ⁻¹ᵁ V) y =
      ((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hj)).hom.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorComp (Y.homOfLE hV) (incO U j O hj)).inv.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j)).app ((Y.homOfLE hV)
            ''ᵁ (V.ι ⁻¹ᵁ V))
      (((restrictFunctorComp (Y.homOfLE hV) (incO U i O hi)).hom.app (Dobj U D i)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hi).symm).hom.app (Dobj U D i)).app
        (V.ι ⁻¹ᵁ V) y)))) := by
    intro y; rw [τ_hom_eq, loc]; rfl
  have c1 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV
    hi).symm (Dobj U D i)
  have c2 := restrictFunctorComp_hom_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U i O hi) (Dobj
    U D i)
  have c3 := restrictFunctorComp_inv_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U j O hj) (Dobj
    U D j)
  have c4 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV hj)
    (Dobj U D j)
  have hEv := ev ((Dobj U D i).presheaf.map
    (homOfLE (T_le_in U i V (hV.trans hi) V)).op x)
  have hOuter := congrArg
    (fun y : Γ((Dobj U D j).restrict (incO U j V (hV.trans hj)), V.ι ⁻¹ᵁ V) =>
      (Dobj U D j).presheaf.map
        (homOfLE (T_le_out U j V (hV.trans hj) V le_rfl)).op y) hEv
  refine hOuter.trans ?_
  erw [c1, c2, c3, c4, ← τ_hom_eq]
  generalize (τ U D i j O hi hj).hom = τ₀
  refine (map_map _ _ _ _).trans ((map_map _ _ _ _).trans ?_)
  erw [map_map (Dobj U D i), map_map (Dobj U D i)]
  erw [presheaf_map_congr (Dobj U D i) _
    ((Hom.opensFunctor (incO U i O hi)).map (homOfLE hsub) ≫ homOfLE (T_le_in U i O hi V)) x]
  erw [← map_map (Dobj U D i) (homOfLE (T_le_in U i O hi V)) ((Hom.opensFunctor (incO U i O
    hi)).map (homOfLE hsub)) x]
  have nat := app_presheaf_map τ₀ (homOfLE hsub)
    ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  rw [restrict_map, restrict_map] at nat
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem presheaf_map_injective_of_eq' {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' =
    V) (f : V' ⟶ V) :
    Function.Injective (M.presheaf.map f.op) := by
  subst e
  intro x y hxy
  rwa [map_self, map_self] at hxy

theorem preimage_ι_inf_self (O W : Y.Opens) : O.ι ⁻¹ᵁ (W ⊓ O) = O.ι ⁻¹ᵁ W := by
  change O.ι ⁻¹ᵁ W ⊓ O.ι ⁻¹ᵁ O = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem compat_of_T (W : Y.Opens) (s : ∀ i, Γ(P U D i, W)) (i j : ι)
    (h : T U D i j (U i ⊓ U j) inf_le_left inf_le_right (W ⊓ (U i ⊓ U j)) inf_le_right
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op (s i)) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono inf_le_left)).op (s j)) :
    (α U D i j).app W (s i) = (β U D i j).app W (s j) := by
  rw [α_app, β_app]
  have hm : (U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j)) ≤ (U i ⊓ U j).ι ⁻¹ᵁ W :=
    (U i ⊓ U j).ι.preimage_mono inf_le_left
  have he : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))) =
      (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
    rw [preimage_ι_inf_self]
  let a : (Dobj U D i).presheaf.obj
      (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) ⟶
      (Dobj U D j).presheaf.obj
        (op ((p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) :=
    (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j)))
  let aW : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W))) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W))) :=
    (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W)
  change aW ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i)) =
    (Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op (s j)
  apply presheaf_map_injective_of_eq' (Dobj U D j) he
    ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm))
  have nat : a ((Dobj U D i).presheaf.map
      ((Hom.opensFunctor (p₁ U i j)).map (homOfLE hm)).op
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))) =
      (Dobj U D j).presheaf.map ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm)).op
        (aW ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))) :=
    app_presheaf_map (ρ U D i j).hom (homOfLE hm)
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))
  rw [← nat]
  have hR := map_map (Dobj U D j) (homOfLE (β_le U i j W))
    ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm))
    (show (Dobj U D j).presheaf.obj (op ((U j).ι ⁻¹ᵁ W)) from s j)
  refine Eq.trans ?_ hR.symm
  have eL : (Dobj U D i).presheaf.map
      ((Hom.opensFunctor (p₁ U i j)).map (homOfLE hm)).op
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i)) =
      (Dobj U D i).presheaf.map
        (homOfLE (T_le_in U i (U i ⊓ U j) inf_le_left (W ⊓ (U i ⊓ U j)))).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op
          (s i)) :=
    (map_map _ _ _ _).trans
      ((presheaf_map_congr _ _ _ _).trans (map_map _ _ _ _).symm)
  refine (congrArg
    (fun x : (Dobj U D i).presheaf.obj
        (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) => a x) eL).trans ?_
  change (Dobj U D j).presheaf.map
      (homOfLE (T_le_out U j (U i ⊓ U j) inf_le_right
        (W ⊓ (U i ⊓ U j)) inf_le_right)).op
      (a ((Dobj U D i).presheaf.map
        (homOfLE (T_le_in U i (U i ⊓ U j) inf_le_left (W ⊓ (U i ⊓ U j)))).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op
          (s i)))) =
    (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono inf_le_left)).op (s j) at h
  have h' := congrArg ((Dobj U D j).presheaf.map
    (homOfLE (T_le_in U j (U i ⊓ U j) inf_le_right (W ⊓ (U i ⊓ U j)))).op) h
  have h'' := (map_map_self (Dobj U D j) _ _ _).symm.trans
    (h'.trans (map_map (Dobj U D j) _ _ _))
  refine h''.trans ?_
  exact presheaf_map_congr _ _ _ _

/-- Restrict the glued sheaf to a covering open and project to its descent component. -/
noncomputable def restrictGluedHom (k : ι) : (glued U D).restrict (incl U k) ⟶ Dobj U D k :=
  (restrictFunctor (incl U k)).map (proj U D k) ≫ (restrictAdjunction (incl U k)).counit.app (Dobj
    U D k)

theorem restrictGluedHom_app (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens)
    (s : compatible U D ((incl U k) ''ᵁ V)) :
    (restrictGluedHom U D k).app V (show Γ((glued U D).restrict (incl U k), V) from s) =
      (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op (s.1 k) := by
  have h := restrictAdjunction_counit_app_app (incl U k) (Dobj U D k) V
  rw [restrictGluedHom, Scheme.Modules.Hom.comp_app]
  erw [h]
  rfl

theorem restrictGluedHom_app_injective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Injective ((restrictGluedHom U D k).app V) := by
  intro s s' h
  change compatible U D ((incl U k) ''ᵁ V) at s s'
  rw [restrictGluedHom_app, restrictGluedHom_app] at h
  have hinj : Function.Injective ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq
    V).symm).op) := by
    intro x y hxy
    simpa using congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op)
      hxy
  exact compatible_ext_of_le U D
    ((incl U k).image_le_opensRange V |>.trans (Scheme.Opens.opensRange_ι _).le) (hinj h)

theorem preimage_incl_inf_self (i : ι) (W : Y.Opens) : (U i).ι ⁻¹ᵁ (W ⊓ U i) = (U i).ι ⁻¹ᵁ W := by
  change (U i).ι ⁻¹ᵁ W ⊓ (U i).ι ⁻¹ᵁ (U i) = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem restrictGluedHom_app_surjective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Surjective ((restrictGluedHom U D k).app V) := by
  intro y
  have hW : (incl U k) ''ᵁ V ≤ U k :=
    ((incl U k).image_le_opensRange V).trans (Scheme.Opens.opensRange_ι _).le
  let t : Γ(P U D k, (incl U k) ''ᵁ V) :=
    (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op y
  let s : ∀ i, Γ(P U D i, (incl U k) ''ᵁ V) := fun i =>
    (Dobj U D i).presheaf.map (homOfLE (preimage_incl_inf_self U i _).symm.le).op
      (T U D k i (U k ⊓ U i) inf_le_left inf_le_right ((incl U k) ''ᵁ V ⊓ U i) (inf_le_inf_right
        (U i) hW)
        ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono inf_le_left)).op t))
  have step : ∀ (i : ι) (V' : Y.Opens) (hV'W : V' ≤ (incl U k) ''ᵁ V) (hV'i : V' ≤ U i),
      (Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV'W)).op (s i) =
        T U D k i V' (hV'W.trans hW) hV'i V' le_rfl
          ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono hV'W)).op t) := by
    intro i V' hV'W hV'i
    have hle : V' ≤ (incl U k) ''ᵁ V ⊓ U i := le_inf hV'W hV'i
    refine (map_map _ _ _ _).trans ?_
    refine (presheaf_map_congr _ _ (homOfLE ((U i).ι.preimage_mono hle)) _).trans ?_
    refine (T_res U D k i (U k ⊓ U i) inf_le_left inf_le_right (inf_le_inf_right (U i) hW) hle
      _).symm.trans ?_
    refine (congrArg (T U D k i (U k ⊓ U i) inf_le_left inf_le_right _ (hle.trans
      (inf_le_inf_right (U i) hW)))
      ((map_map _ _ _ _).trans (presheaf_map_congr _ _ (homOfLE ((U k).ι.preimage_mono hV'W))
        _))).trans ?_
    exact T_indep U D k i _ _ _ _ _ _
  have mem : s ∈ compatible U D ((incl U k) ''ᵁ V) := by
    intro i j
    apply compat_of_T
    rw [step i _ inf_le_left (inf_le_right.trans inf_le_left), step j _ inf_le_left
      (inf_le_right.trans inf_le_right),
      T_indep, T_comp]
  refine ⟨⟨s, mem⟩, ?_⟩
  rw [restrictGluedHom_app]
  have hk : s k = t :=
    (congrArg ((Dobj U D k).presheaf.map (homOfLE (preimage_incl_inf_self U k _).symm.le).op)
      (T_self U D k (U k ⊓ U k) inf_le_left ((incl U k) ''ᵁ V ⊓ U k) (inf_le_inf_right (U k) hW)
        _)).trans
      (map_map_self _ _ _ _)
  exact (congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op)
    hk).trans
    (map_map_self _ _ _ _)

theorem isIso_restrictGluedHom (k : ι) : IsIso (restrictGluedHom U D k) := by
  refine Hom.isIso_iff_isIso_app.mpr fun V => ?_
  have : IsIso ((CategoryTheory.forget Ab).map ((restrictGluedHom U D k).app V)) :=
    (isIso_iff_bijective _).mpr ⟨restrictGluedHom_app_injective U D k V,
      restrictGluedHom_app_surjective U D k V⟩
  exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)

/-- The isomorphism from the pullback of the glued sheaf to a descent component. -/
noncomputable def gluedIso (k : ι) : (Modules.pullback (incl U k)).obj (glued U D) ≅ Dobj U D k :=
  ((restrictFunctorIsoPullback (incl U k)).app (glued U D)).symm ≪≫
    @asIso _ _ _ _ (restrictGluedHom U D k) (isIso_restrictGluedHom U D k)

theorem image_mono' {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {A B : X.Opens} (h : A ≤
    B) :
    f ''ᵁ A ≤ f ''ᵁ B := fun _ ⟨z, hz, e⟩ => ⟨z, h hz, e⟩

theorem cs_le (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₁ U i j) ''ᵁ V ≤ (U i).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₁ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (α_le U i j _)

theorem cs_le' (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₂ U i j) ''ᵁ V ≤ (U j).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₂ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (β_le U i j _)


theorem comm_sections (i j : ι) :
    castComp (p₁ U i j) (incl U i) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_left) (glued U D) ≫
        (restrictFunctor (p₁ U i j)).map (restrictGluedHom U D i) ≫ (ρ U D i j).hom =
      castComp (p₂ U i j) (incl U j) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_right) (glued U D) ≫
        (restrictFunctor (p₂ U i j)).map (restrictGluedHom U D j) := by
  apply Scheme.Modules.hom_ext
  intro V
  apply AddCommGrpCat.ext
  intro s
  change compatible U D ((U i ⊓ U j).ι ''ᵁ V) at s
  generalize hρ : (ρ U D i j).hom = ρ₀
  have E₁ : (incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₁ U i j) (incl U i) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_left) V
  have E₂ : (incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₂ U i j) (incl U j) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_right) V
  let ci : (glued U D).presheaf.obj (op ((U i ⊓ U j).ι ''ᵁ V)) ⟶
      (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) :=
    (castComp (p₁ U i j) (incl U i) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_left) (glued U D)).app V
  let cj : (glued U D).presheaf.obj (op ((U i ⊓ U j).ι ''ᵁ V)) ⟶
      (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) :=
    (castComp (p₂ U i j) (incl U j) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_right) (glued U D)).app V
  let ri : (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) ⟶
      (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) :=
    (restrictGluedHom U D i).app ((p₁ U i j) ''ᵁ V)
  let rj : (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ V)) :=
    (restrictGluedHom U D j).app ((p₂ U i j) ''ᵁ V)
  let aρ : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ V)) :=
    ρ₀.app V
  change (ci ≫ ri ≫ aρ) s = (cj ≫ rj) s
  change aρ (ri (ci s)) = rj (cj s)
  have k1 : ci s = (glued U D).presheaf.map (eqToHom E₁).op s :=
    castComp_app (p₁ U i j) (incl U i) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_left) (glued U D) V s
  have k2 : cj s = (glued U D).presheaf.map (eqToHom E₂).op s :=
    castComp_app (p₂ U i j) (incl U j) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_right) (glued U D) V s
  refine (congrArg
    (fun x : (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) =>
      aρ (ri x)) k1).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun x : (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) =>
      rj x) k2).symm
  have r1 : ri ((glued U D).presheaf.map (eqToHom E₁).op s) =
      (Dobj U D i).presheaf.map
        (eqToHom ((incl U i).preimage_image_eq ((p₁ U i j) ''ᵁ V)).symm).op
        ((show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from
          (glued U D).presheaf.map (eqToHom E₁).op s).1 i) :=
    restrictGluedHom_app U D i ((p₁ U i j) ''ᵁ V)
      (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from
        (glued U D).presheaf.map (eqToHom E₁).op s)
  have r2 : rj ((glued U D).presheaf.map (eqToHom E₂).op s) =
      (Dobj U D j).presheaf.map
        (eqToHom ((incl U j).preimage_image_eq ((p₂ U i j) ''ᵁ V)).symm).op
        ((show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from
          (glued U D).presheaf.map (eqToHom E₂).op s).1 j) :=
    restrictGluedHom_app U D j ((p₂ U i j) ''ᵁ V)
      (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from
        (glued U D).presheaf.map (eqToHom E₂).op s)
  refine (congrArg
    (fun x : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) => aρ x) r1).trans ?_
  refine Eq.trans ?_ r2.symm
  have g1 : (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from (glued U D).presheaf.map
    (eqToHom E₁).op s).1 i =
      (Dobj U D i).presheaf.map ((Opens.map (incl U i).base).map (eqToHom E₁)).op (s.1 i) := rfl
  have g2 : (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from (glued U D).presheaf.map
    (eqToHom E₂).op s).1 j =
      (Dobj U D j).presheaf.map ((Opens.map (incl U j).base).map (eqToHom E₂)).op (s.1 j) := rfl
  erw [g1, g2]
  erw [map_map (Dobj U D i), map_map (Dobj U D j)]
  erw [presheaf_map_congr (Dobj U D i) _ (homOfLE (cs_le U i j V)) (s.1 i),
    presheaf_map_congr (Dobj U D j) _ (homOfLE (cs_le' U i j V)) (s.1 j)]
  have hc := s.2 i j
  rw [α_app, β_app] at hc
  rw [hρ] at hc
  have nat := app_presheaf_map ρ₀ (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))
    ((Dobj U D i).presheaf.map (homOfLE (α_le U i j _)).op (s.1 i))
  rw [restrict_map, restrict_map] at nat
  erw [hc] at nat
  erw [presheaf_map_congr (Dobj U D i) (homOfLE (cs_le U i j V))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm)) ≫
      homOfLE (α_le U i j _)) (s.1 i)]
  erw [← map_map (Dobj U D i) (homOfLE (α_le U i j ((U i ⊓ U j).ι ''ᵁ V)))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))) (s.1
      i)]
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)


end Opens
end AlgebraicGeometry.Scheme.Modules.ObjGlue
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover
end ProofImplementation
