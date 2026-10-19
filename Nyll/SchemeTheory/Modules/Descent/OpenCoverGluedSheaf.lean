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

import Nyll.SchemeTheory.Modules.Descent.ToDescentDataMapBijective
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Forget
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Sieves.Presieve
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Image
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Lattice
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Choose
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
/-!
Effectivity of descent data for sheaves of scheme modules on an open cover.
Compatible local sections form the glued sheaf and recover the prescribed transitions.
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

theorem pullHom_comp' ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ :
    F.obj (.mk (op X₃))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (a ≫ b) g gf₁ gf₃ h₁ h₃ = pullHom a g gf₁ gf₂ h₁ h₂ ≫ pullHom b g gf₂ gf₃ h₂ h₃ := by
  simp only [pullHom, Functor.map_comp, Category.assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]

theorem map_map_eq_pullHom ⦃X Y : C⦄ (f : Y ⟶ X) ⦃M N : F.obj (.mk (op X))⦄ (ψ : M ⟶ N) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    (F.map gf.op.toLoc).toFunctor.map ψ = pullHom ((F.map f.op.toLoc).toFunctor.map ψ) g gf gf hgf
      hgf := by
  dsimp only [pullHom]
  rw [← Category.assoc, ← F.mapComp'_hom_naturality f.op.toLoc g.op.toLoc gf.op.toLoc (
    by rw [← hgf]; rfl) ψ,
    Category.assoc]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

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

/-- The canonical pseudofunctor of scheme modules used by the descent data. -/
noncomputable abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Mdl.{u}

theorem keyMC {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : MOD.obj a) :
    (MOD.mapComp' u' v' (u' ≫ v') rfl).hom.toNatTrans.app M = (MOD.mapComp u'
      v').hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem mapComp'_hom_app_eq {X X' Z : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ Z) (L : Z.Modules) (fg :
    X ⟶ Z) (h : f ≫ g = fg) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L
      := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact keyMC g.op.toLoc f.op.toLoc L


theorem crux_MOD {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (gf₁ : Z' ⟶ X₁) (gf₂ : Z' ⟶ X₂) [IsOpenImmersion e] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (h₁ : e ≫ f₁ = gf₁) (h₂ : e ≫ f₂ = gf₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (MOD.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (MOD.map f₂.op.toLoc).toFunctor.obj M₂) :
    (restrictFunctorIsoPullback gf₁).hom.app M₁ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := MOD) φ e gf₁ gf₂ h₁ h₂ ≫
        (restrictFunctorIsoPullback gf₂).inv.app M₂ =
      (restrictFunctorCongr h₁.symm).hom.app M₁ ≫ (restrictFunctorComp e f₁).hom.app M₁ ≫
        (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁ ≫ φ ≫
          (restrictFunctorIsoPullback f₂).inv.app M₂) ≫
        (restrictFunctorComp e f₂).inv.app M₂ ≫ (restrictFunctorCongr h₂).hom.app M₂ :=
  restrictFunctorIsoPullback_conj_pullHom e f₁ f₂ gf₁ gf₂ h₁ h₂ M₁ M₂ φ

section WLOG
variable {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i,
  IsOpenImmersion (g i)]

/-- The opens occurring as ranges of the given family of open immersions. -/
abbrev Ranges : Type u := {O : Y.Opens // ∃ i, (g i).opensRange = O}

theorem sieve_ofArrows_eq_opensRange :
    Sieve.ofArrows _ g = Sieve.ofArrows (fun O : Ranges g => ((O.1 : Y.Opens) : Scheme.{u})) (fun
      O => O.1.ι) := by
  apply le_antisymm
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨i⟩
    exact ⟨_, (g i).isoOpensRange.hom, (⟨(g i).opensRange, i, rfl⟩ : Ranges g).1.ι,
      Presieve.ofArrows.mk (⟨(g i).opensRange, i, rfl⟩ : Ranges g), (g i).isoOpensRange_hom_ι⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨O⟩
    obtain ⟨O, i, rfl⟩ := O
    exact ⟨_, (g i).isoOpensRange.inv, g i, Presieve.ofArrows.mk i, (g i).isoOpensRange_inv_comp⟩
omit [∀ i, IsOpenImmersion (g i)] in
theorem essSurj_iff_of_sieve_eq {ι' : Type v'} {V' : ι' → Scheme.{u}} (g' : ∀ i, V' i ⟶ Y)
    (h : Sieve.ofArrows _ g = Sieve.ofArrows _ g') :
    (MOD.toDescentData g).EssSurj ↔ (MOD.toDescentData g').EssSurj := by
  obtain ⟨e, ⟨iso⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq MOD g g' h
  constructor
  · intro _
    have : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_comp _ _
    exact Functor.essSurj_of_iso iso
  · intro _
    have : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_of_iso iso.symm
    exact Functor.essSurj_of_comp_fully_faithful _ e.functor

end WLOG

section Opens
variable {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)

/-- The inclusion of an open from the covering family into the ambient scheme. -/
abbrev incl (i : ι) : (U i : Scheme.{u}) ⟶ Y := (U i).ι

/-- The inclusion of a pairwise intersection into its first covering open. -/
noncomputable abbrev p₁ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U i : Scheme.{u}) :=
  Y.homOfLE inf_le_left
/-- The inclusion of a pairwise intersection into its second covering open. -/
noncomputable abbrev p₂ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U j : Scheme.{u}) :=
  Y.homOfLE inf_le_right

variable (D : (MOD.{u}).DescentData (incl U))

/-- The module attached to a covering open by the given descent datum. -/
noncomputable abbrev Dobj (i : ι) : ((U i : Y.Opens) : Scheme.{u}).Modules := D.obj i

theorem D_pullHom ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y) (hq : φ ≫ q = q') ⦃i
    j : ι⦄
    (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q) (hf₂ :
      f₂ ≫ incl U j = q)
    (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ : φ ≫ f₁ = g₁) (hg₂ : φ ≫
      f₂ = g₂)
    (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (D.hom q f₁ f₂ hf₁ hf₂) φ g₁ g₂ hg₁ hg₂ =
      D.hom q' g₁ g₂ hg₁' hg₂' :=
  D.pullHom_hom φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂

theorem ofObj_pullHom (M : Y.Modules) ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y)
    (hq : φ ≫ q = q')
    ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q)
    (hf₂ : f₂ ≫ incl U j = q) (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ :
      φ ≫ f₁ = g₁)
    (hg₂ : φ ≫ f₂ = g₂) (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂
      hf₁ hf₂) φ g₁ g₂
        hg₁ hg₂ = ((MOD.toDescentData (incl U)).obj M).hom q' g₁ g₂ hg₁' hg₂' :=
  D_pullHom U ((MOD.toDescentData (incl U)).obj M) φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂ hg₁' hg₂'

theorem ofObj_hom_eq (M : Y.Modules) ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄
    (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u}))
    (hf₁ : f₁ ≫ incl U i = q) (hf₂ : f₂ ≫ incl U j = q) {N : Z.Modules}
    (φ : (Modules.pullback f₂).obj ((Modules.pullback (incl U j)).obj M) ⟶ N) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom
      (X := Z)
      ((Modules.pullback f₁).obj ((Modules.pullback (incl U i)).obj M)) N)
      (((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂ hf₁ hf₂ ≫ φ)
      ((((Scheme.Modules.pullbackComp f₁ (incl U i)).hom.app M ≫
          (Scheme.Modules.pullbackCongr hf₁).hom.app M) ≫
        (Scheme.Modules.pullbackCongr hf₂.symm).hom.app M ≫
        (Scheme.Modules.pullbackComp f₂ (incl U j)).inv.app M) ≫ φ) := by
  rw [← Mdl_mapComp'_inv_app f₁ (incl U i) M q hf₁, ← Mdl_mapComp'_hom_app f₂ (incl U j) M q hf₂]
  rfl

/-- The inclusion of a smaller open into a specified covering open. -/
noncomputable abbrev incO (i : ι) (O : Y.Opens) (h : O ≤ U i) : (O : Scheme.{u}) ⟶ (U i :
  Scheme.{u}) := Y.homOfLE h

theorem incO_comp (i : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) :
    Y.homOfLE hO' ≫ incO U i O hi = incO U i O' (hO'.trans hi) :=
  Scheme.homOfLE_homOfLE Y hO' hi

/-- The descent transition expressed through the restriction--pullback comparisons. -/
noncomputable def τ (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) :
    (Dobj U D i).restrict (incO U i O hi) ≅ (Dobj U D j).restrict (incO U j O hj) :=
  (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i) ≪≫
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≪≫
    ((restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)).symm

/-- The descent transition on the intersection of two covering opens. -/
noncomputable abbrev ρ (i j : ι) : (Dobj U D i).restrict (p₁ U i j) ≅ (Dobj U D j).restrict (p₂ U
  i j) :=
  τ U D i j (U i ⊓ U j) inf_le_left inf_le_right

theorem τ_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) :
    (τ U D i i O hi hi).hom = 𝟙 ((Dobj U D i).restrict (incO U i O hi)) := by
  let e : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let d : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    D.iso O.ι (incO U i O hi) (incO U i O hi) (Y.homOfLE_ι hi) (Y.homOfLE_ι hi)
  have h : d.hom = 𝟙 ((Modules.pullback (incO U i O hi)).obj (Dobj U D i)) :=
    D.hom_self O.ι (incO U i O hi) (Y.homOfLE_ι hi)
  change (e ≪≫ d ≪≫ e.symm).hom = 𝟙 _
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [h, Category.id_comp]
  exact e.hom_inv_id

theorem ρ_self (i : ι) : (ρ U D i i).hom = 𝟙 ((Dobj U D i).restrict (p₁ U i i)) := τ_self U D i _ _

theorem τ_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) :
    (τ U D i j O hi hj).hom ≫ (τ U D j k O hj hk).hom = (τ U D i k O hi hk).hom := by
  let ei : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let ej : (Dobj U D j).restrict (incO U j O hj) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    (restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)
  let ek : (Dobj U D k).restrict (incO U k O hk) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    (restrictFunctorIsoPullback (incO U k O hk)).app (Dobj U D k)
  let dij : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj)
  let djk : (Modules.pullback (incO U j O hj)).obj (Dobj U D j) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    D.iso O.ι (incO U j O hj) (incO U k O hk) (Y.homOfLE_ι hj) (Y.homOfLE_ι hk)
  let dik : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    D.iso O.ι (incO U i O hi) (incO U k O hk) (Y.homOfLE_ι hi) (Y.homOfLE_ι hk)
  have h : dij.hom ≫ djk.hom = dik.hom :=
    D.hom_comp O.ι (incO U i O hi) (incO U j O hj) (incO U k O hk)
      (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (Y.homOfLE_ι hk)
  change (ei ≪≫ dij ≪≫ ej.symm).hom ≫ (ej ≪≫ djk ≪≫ ek.symm).hom =
    (ei ≪≫ dik ≪≫ ek.symm).hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ej.inv_hom_id_assoc, reassoc_of% h]

/-- Push the module on a covering open forward to the ambient scheme. -/
noncomputable abbrev P (i : ι) : Y.Modules := (pushforward (incl U i)).obj (Dobj U D i)
/-- Push the second module restricted to an overlap forward to the ambient scheme. -/
noncomputable abbrev Q (i j : ι) : Y.Modules := (pushforward (U i ⊓ U j).ι).obj ((Dobj U D
  j).restrict (p₂ U i j))

/-- Restrict the second covering module to the overlap and push it forward. -/
noncomputable def β (i j : ι) : P U D j ⟶ Q U D i j :=
  (pushforward (incl U j)).map ((restrictAdjunction (p₂ U i j)).unit.app (Dobj U D j)) ≫
    (pushforwardComp (p₂ U i j) (incl U j)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_right)).hom.app _

/-- Restrict the first covering module and transport it by the overlap transition. -/
noncomputable def α (i j : ι) : P U D i ⟶ Q U D i j :=
  ((pushforward (incl U i)).map ((restrictAdjunction (p₁ U i j)).unit.app (Dobj U D i)) ≫
    (pushforwardComp (p₁ U i j) (incl U i)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_left)).hom.app _) ≫
    (pushforward (U i ⊓ U j).ι).map (ρ U D i j).hom

/-- The submodule of families of sections satisfying all overlap compatibility equations. -/
noncomputable def compatible (W : Y.Opens) : Submodule Γ(Y, W) (∀ i, Γ(P U D i, W)) where
  carrier := {s | ∀ i j, (α U D i j).app W (s i) = (β U D i j).app W (s j)}
  add_mem' := by
    intro s t hs ht i j
    simp only [Pi.add_apply, map_add, hs i j, ht i j]
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro r s hs i j
    simp only [Pi.smul_apply, Hom.app_smul, hs i j]

theorem app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ⟶
    W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map h.op x) = N.presheaf.map h.op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality h.op) x

theorem compatible_map {W W' : Y.Opens} (h : W' ⟶ W) (s : ∀ i, Γ(P U D i, W)) (hs : s ∈ compatible
    U D W) :
    (fun i => (P U D i).presheaf.map h.op (s i)) ∈ compatible U D W' := by
  intro i j
  change (α U D i j).app W' ((P U D i).presheaf.map h.op (s i)) = (β U D i j).app W' ((P U D
    j).presheaf.map h.op (s j))
  rw [app_presheaf_map, app_presheaf_map, hs i j]

/-- The abelian presheaf of compatible families of sections. -/
noncomputable def gluedAb : (TopologicalSpace.Opens Y)ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (compatible U D W.unop)
  map {W W'} h := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun i => (P U D i).presheaf.map h (s.1 i), compatible_map U D h.unop s.1
      s.2⟩
      map_zero' := by
        apply Subtype.ext; funext i
        exact map_zero ((P U D i).presheaf.map h).hom
      map_add' := by
        intro s t; apply Subtype.ext; funext i
        exact map_add ((P U D i).presheaf.map h).hom (s.1 i) (t.1 i) }
  map_id W := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    exact ConcreteCategory.congr_hom ((P U D i).presheaf.map_id W) (s.1 i)
  map_comp {W W' W''} h h' := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    exact ConcreteCategory.congr_hom ((P U D i).presheaf.map_comp h h') (s.1 i)

theorem gluedAb_map_apply_coe {W W' : (TopologicalSpace.Opens Y)ᵒᵖ} (h : W ⟶ W') (s : compatible U
    D W.unop) (i : ι) :
    ((gluedAb U D).map h s).1 i = (P U D i).presheaf.map h (s.1 i) := rfl

/-- The presheaf of modules whose sections are compatible families. -/
noncomputable def gluedPresheaf : Y.PresheafOfModules :=
  @PresheafOfModules.ofPresheaf _ _ _ (gluedAb U D)
    (fun W => show Module Γ(Y, W.unop) (compatible U D W.unop) from inferInstance)
    (by
      intro W W' h r s
      apply Subtype.ext; funext i
      exact (P U D i).map_smul h.unop r (s.1 i))

/-- The underlying abelian sheaf of a sheaf of scheme modules. -/
noncomputable abbrev abSheaf (M : Y.Modules) : TopCat.Sheaf Ab Y.toTopCat := ⟨M.presheaf, M.isSheaf⟩

theorem isSheaf_gluedPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (gluedPresheaf U D).presheaf := by
  change TopCat.Presheaf.IsSheaf (gluedAb U D)
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc : ∀ i, TopCat.Presheaf.IsCompatible (P U D i).presheaf W (fun a => (sf a).1 i) :=
    fun i a b => congrArg (fun s : compatible U D _ => s.1 i) (hsf a b)
  choose t ht huniq using fun i => (abSheaf (P U D i)).existsUnique_gluing W (fun a => (sf a).1 i)
    (hc i)
  have hmem : t ∈ compatible U D (iSup W) := by
    intro i j
    apply (abSheaf (Q U D i j)).eq_of_locally_eq W
    intro a
    change (Q U D i j).presheaf.map (Opens.leSupr W a).op ((α U D i j).app (iSup W) (t i)) =
      (Q U D i j).presheaf.map (Opens.leSupr W a).op ((β U D i j).app (iSup W) (t j))
    rw [← app_presheaf_map, ← app_presheaf_map]
    erw [ht i a, ht j a]
    exact (sf a).2 i j
  refine ⟨⟨t, hmem⟩, fun a => ?_, fun y hy => ?_⟩
  · apply Subtype.ext; funext i; exact ht i a
  · apply Subtype.ext; funext i
    exact huniq i _ (fun a => congrArg (fun s : compatible U D _ => s.1 i) (hy a))

/-- The sheaf of modules formed by gluing compatible families of sections. -/
noncomputable def glued : Y.Modules := ⟨gluedPresheaf U D, isSheaf_gluedPresheaf U D⟩

theorem glued_presheaf_obj (W : Y.Opens) : ((glued U D).presheaf.obj (op W) : Type u) = compatible
    U D W := rfl

/-- The projection from compatible families to one pushed-forward component. -/
noncomputable def projAb (k : ι) : gluedAb U D ⟶ (P U D k).presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s => s.1 k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  naturality {W W'} h := by apply AddCommGrpCat.ext; intro s; rfl

/-- The module morphism projecting the glued sheaf onto a pushed-forward component. -/
noncomputable def proj (k : ι) : glued U D ⟶ P U D k :=
  ⟨PresheafOfModules.homMk (M₁ := (glued U D).val) (M₂ := (P U D k).val) (projAb U D k)
    (fun _W _r _s => rfl)⟩

theorem proj_app (k : ι) (W : Y.Opens) (s : compatible U D W) :
    (proj U D k).app W (show Γ(glued U D, W) from s) = s.1 k := rfl

theorem presheaf_map_congr {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (f g : V' ⟶ V) (x :
    Γ(M, V)) :
    M.presheaf.map f.op x = M.presheaf.map g.op x := by rw [Subsingleton.elim f g]

theorem preimage_comp' {X X' X'' : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ X'') (W : X''.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := rfl

theorem preimage_ι_inf_right (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₂ U i j) ⁻¹ᵁ ((U j).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem preimage_ι_inf_left (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₁ U i j) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem β_le (i j : ι) (W : Y.Opens) : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right]; exact Scheme.Hom.image_preimage_le _ _

theorem α_le (i j : ι) (W : Y.Opens) : (p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U i).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_left]; exact Scheme.Hom.image_preimage_le _ _

theorem β_eq_of_le {i j : ι} {W : Y.Opens} (hW : W ≤ U i) :
    (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) = (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  change (U j).ι ⁻¹ᵁ W ≤ (U j).ι ⁻¹ᵁ (U i ⊓ U j)
  have h1 : (U j).ι ⁻¹ᵁ (U i ⊓ U j) = (U j).ι ⁻¹ᵁ (U i) ⊓ (U j).ι ⁻¹ᵁ (U j) := rfl
  rw [h1, Scheme.Opens.ι_preimage_self, inf_top_eq]
  exact fun y hy => hW hy

theorem β_app_hom (i j : ι) (W : Y.Opens) :
    (β U D i j).app W = (Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op := by
  have h1 := restrictAdjunction_unit_app_app (p₂ U i j) (Dobj U D j) ((U j).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j)) (p₂ U i j) (incl
    U j) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j))
    (Y.homOfLE_ι (inf_le_right : U i ⊓ U j ≤ U j)) W
  rw [β, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine ((Dobj U D j).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem β_app (i j : ι) (W : Y.Opens) (x : Γ(P U D j, W)) :
    (β U D i j).app W x = ((Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op x :) :=
  ConcreteCategory.congr_hom (β_app_hom U D i j W) x

theorem α_app_hom (i j : ι) (W : Y.Opens) :
    (α U D i j).app W = (Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op ≫
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
  have h1 := restrictAdjunction_unit_app_app (p₁ U i j) (Dobj U D i) ((U i).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j)) (p₁ U i j) (incl
    U i) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j))
    (Y.homOfLE_ι (inf_le_left : U i ⊓ U j ≤ U i)) W
  rw [α, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app, pushforward_map_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine congrArg (fun t => t ≫ Hom.app (ρ U D i j).hom ((U i ⊓ U j).ι ⁻¹ᵁ W)) ?_
  refine ((Dobj U D i).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem α_app (i j : ι) (W : Y.Opens) (x : Γ(P U D i, W)) :
    (α U D i j).app W x =
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) ((Dobj U D i).presheaf.map (homOfLE (α_le U i j
        W)).op x) :=
  ConcreteCategory.congr_hom (α_app_hom U D i j W) x

theorem restrictFunctor_map_app {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (t : M ⟶ N)
    (V : X.Opens) : ((restrictFunctor f).map t).app V = t.app (f ''ᵁ V) := rfl

theorem presheaf_map_injective_of_eq {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' =
    V) (h : V' ≤ V) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  subst e
  intro x y hxy
  simpa using hxy

theorem compatible_ext_of_le {k : ι} {W : Y.Opens} (hW : W ≤ U k) {s s' : compatible U D W}
    (h : s.1 k = s'.1 k) : s = s' := by
  apply Subtype.ext; funext i
  have hs := s.2 k i
  have hs' := s'.2 k i
  rw [h, hs'] at hs
  rw [β_app, β_app] at hs
  exact (presheaf_map_injective_of_eq (Dobj U D i) (β_eq_of_le U hW) (β_le U k i W) hs).symm

theorem map_map {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (f : V₂ ⟶ V₁) (g : V₃ ⟶ V₂)
    (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map (g ≫ f).op x :=
  (ConcreteCategory.congr_hom (M.presheaf.map_comp f.op g.op) x).symm

theorem map_self {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} (f : V ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 V)]
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (op V)) x

theorem map_map_self {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ : X.Opens} (f : V₂ ⟶ V₁) (g : V₁ ⟶
    V₂) (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = x := by
  rw [map_map, map_self]


end Opens
end AlgebraicGeometry.Scheme.Modules.ObjGlue
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover
end ProofImplementation
