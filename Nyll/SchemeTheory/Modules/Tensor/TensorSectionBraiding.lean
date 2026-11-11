/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-!
# Braiding on the actual tensor sections of module sheaves

The native monoidal sheafification functor is braided. Its comparison
with the tensor of sheaves intertwines the original presheaf braiding
and sheaf braiding. Evaluating on the sheafification unit of a pure
tensor proves that braiding exchanges the original two local sections.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

@[instance_reducible] private def sheafifyBraided (X : Scheme.{u}) : (sheafify X).Braided := by
  let : (SheafOfModules.presheafW (Opens.grothendieckTopology X) X.sheaf.obj).IsMonoidal :=
    SheafOfModules.presheafW_isMonoidal (J := Opens.grothendieckTopology X)
      X.sheaf.obj X.ringCatSheaf.property
  exact inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property)
    (W := SheafOfModules.presheafW (Opens.grothendieckTopology X) X.sheaf.obj)
    (SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property)).Braided

private theorem map_braiding_comp_δ {C C' : Type*} [Category C] [Category C']
    [MonoidalCategory C] [MonoidalCategory C'] [BraidedCategory C] [BraidedCategory C']
    (F : C ⥤ C') [F.Braided] (M N : C) :
    F.map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ F N M =
      Functor.OplaxMonoidal.δ F M N ≫ (β_ (F.obj M) (F.obj N)).hom := by
  rw [Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

private theorem tensorIsoSheafify_hom_braiding {X : Scheme.{u}} (L M : X.Modules) :
    (tensorIsoSheafify L M).hom ≫ (β_ L M).hom =
      (sheafify X).map (β_ L.val M.val).hom ≫ (tensorIsoSheafify M L).hom := by
  let : (sheafify X).Braided := sheafifyBraided X
  let eL : (sheafify X).obj L.val ⟶ L :=
    (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).counit.app L
  let eM : (sheafify X).obj M.val ⟶ M :=
    (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).counit.app M
  change (Functor.OplaxMonoidal.δ (sheafify X) L.val M.val ≫ (eL ⊗ₘ eM)) ≫
      (β_ L M).hom =
    (sheafify X).map (β_ L.val M.val).hom ≫
      Functor.OplaxMonoidal.δ (sheafify X) M.val L.val ≫ (eM ⊗ₘ eL)
  rw [Category.assoc, BraidedCategory.braiding_naturality (C := X.Modules) eL eM,
    ← Category.assoc, ← map_braiding_comp_δ, Category.assoc]

local instance presheafSectionsModule {X : Scheme.{u}}
    (P : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

private theorem sheafify_map_app_unit {X : Scheme.{u}}
    {P Q : X.PresheafOfModules} (g : P ⟶ Q) (U : X.Opens) (s : P.obj (op U)) :
    ((sheafify X).map g).val.app (op U)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app
          (op U) s) =
      ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app
        (op U) (g.app (op U) s) := by
  have h := (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.naturality g
  exact (congr($(h.symm).app (op U) s) :)

/-- The actual sheaf braiding swaps the two original local tensor sections. -/
theorem braiding_hom_app_tensorSections {X : Scheme.{u}} {L M : X.Modules}
    {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (β_ L M).hom.app U (tensorSections s t) = tensorSections t s := by
  let adj : sheafify X ⊣ SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property :=
    SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property
  have h := congr($(tensorIsoSheafify_hom_braiding L M).val.app (op U)
    ((adj.unit.app (L.val ⊗ M.val)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))))
  change (β_ L M).hom.val.app (op U)
      ((tensorIsoSheafify L M).hom.val.app (op U)
        ((adj.unit.app (L.val ⊗ M.val)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) =
    (tensorIsoSheafify M L).hom.val.app (op U)
      (((sheafify X).map (β_ L.val M.val).hom).val.app (op U)
        ((adj.unit.app (L.val ⊗ M.val)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) at h
  change (β_ L M).hom.val.app (op U)
      ((tensorIsoSheafify L M).hom.val.app (op U)
        ((adj.unit.app (L.val ⊗ M.val)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) =
    (tensorIsoSheafify M L).hom.val.app (op U)
      ((adj.unit.app (M.val ⊗ L.val)).app (op U)
        ((t : M.val.obj (op U)) ⊗ₜ[Γ(X, U)] (s : L.val.obj (op U))))
  rw [h]
  erw [sheafify_map_app_unit (β_ L.val M.val).hom U]
  rfl

end AlgebraicGeometry.Scheme.Modules
