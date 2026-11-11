/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.SchemeTheory.CategoryTheory.FunctorCategoryExactness
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# The actual cohomology-presheaf boundary of a short exact sequence

The Ext boundary is an additive natural morphism from quotient sections
to the actual degree-one cohomology presheaf. Its kernel is the image
of the middle sheaf's sections. For an injective middle sheaf it presents
the entire cohomology presheaf as a cokernel.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.Abelian

namespace EtaleCohomology

variable (X : Scheme.{u})
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact)

/-- The actual Ext boundary, written on ordinary sections. -/
def cohomologyPresheafSectionBoundary (V : X.Etale) :
    S.X₃.obj.obj (op V) →+ Sheaf.H'.{u} S.X₁ 1 V where
  toFun s := (Ext.mk₀
    ((freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₃).symm s)).comp
      hS.extClass (zero_add 1)
  map_zero' := by
    change (Ext.mk₀
      ((freeAbelianSheafYonedaHomAddEquiv X.smallEtaleTopology V S.X₃).symm 0)).comp _ _ = 0
    rw [map_zero, Ext.mk₀_zero, Ext.zero_comp]
  map_add' s t := by
    change (Ext.mk₀
      ((freeAbelianSheafYonedaHomAddEquiv X.smallEtaleTopology V S.X₃).symm
        (s + t))).comp _ _ = _
    rw [map_add, Ext.mk₀_add, Ext.add_comp]
    rfl

/-- A section has zero boundary precisely when it lifts to the middle sheaf. -/
theorem cohomologyPresheafSectionBoundary_eq_zero_iff
    (V : X.Etale) (s : S.X₃.obj.obj (op V)) :
    cohomologyPresheafSectionBoundary X S hS V s = 0 ↔
      ∃ t, S.g.hom.app (op V) t = s := by
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let e := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₃
  let a : P ⟶ S.X₃ := e.symm s
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ a) rfl h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective P S.X₂).surjective b
    have ht : t ≫ S.g = a :=
      (Ext.mk₀_bijective P S.X₃).injective (by
        simpa only [Ext.mk₀_comp_mk₀] using hb)
    refine ⟨freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₂ t, ?_⟩
    rw [← freeAbelianSheafYonedaHomEquiv_postcomp, ht]
    exact e.apply_symm_apply s
  · rintro ⟨t, ht⟩
    let e₂ := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₂
    let b : P ⟶ S.X₂ := e₂.symm t
    have hb : b ≫ S.g = a := by
      apply e.injective
      rw [freeAbelianSheafYonedaHomEquiv_postcomp]
      change S.g.hom.app (op V) (e₂ (e₂.symm t)) = e (e.symm s)
      rw [e₂.apply_symm_apply, e.apply_symm_apply]
      exact ht
    change (Ext.mk₀ a).comp hS.extClass (zero_add 1) = 0
    rw [← hb, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero]

/-- The actual section boundary commutes with every étale restriction map. -/
theorem cohomologyPresheafSectionBoundary_restrict
    {V W : X.Etale} (f : W ⟶ V) (s : S.X₃.obj.obj (op V)) :
    (S.X₁.cohomologyPresheaf 1).map f.op
      (cohomologyPresheafSectionBoundary X S hS V s) =
        cohomologyPresheafSectionBoundary X S hS W (S.X₃.obj.map f.op s) := by
  let P := freeAbelianSheafYoneda X.smallEtaleTopology
  let eV := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₃
  let eW := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W S.X₃
  let a : P.obj V ⟶ S.X₃ := eV.symm s
  let b : P.obj W ⟶ S.X₃ := eW.symm (S.X₃.obj.map f.op s)
  have hab : P.map f ≫ a = b := by
    apply eW.injective
    rw [freeAbelianSheafYonedaHomEquiv_precomp]
    change S.X₃.obj.map f.op (eV (eV.symm s)) = eW (eW.symm (S.X₃.obj.map f.op s))
    rw [eV.apply_symm_apply, eW.apply_symm_apply]
  change (Ext.mk₀ (P.map f)).comp ((Ext.mk₀ a).comp hS.extClass (zero_add 1))
    (zero_add 1) = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hab]
  rfl

/-- The boundary is a morphism of the actual presheaves. -/
def cohomologyPresheafBoundaryHom :
    S.X₃.obj ⟶ S.X₁.cohomologyPresheaf 1 where
  app V := AddCommGrpCat.ofHom (cohomologyPresheafSectionBoundary X S hS V.unop)
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (cohomologyPresheafSectionBoundary_restrict X S hS f.unop s).symm

/-- An injective middle sheaf makes the section boundary surjective. -/
theorem cohomologyPresheafSectionBoundary_surjective [Injective S.X₂] (V : X.Etale) :
    Function.Surjective (cohomologyPresheafSectionBoundary X S hS V) := by
  intro a
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let e := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₃
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ P hS a
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨f, hf⟩ := (Ext.mk₀_bijective P S.X₃).surjective b
  refine ⟨e f, ?_⟩
  change (Ext.mk₀ (e.symm (e f))).comp hS.extClass (zero_add 1) = a
  rw [e.symm_apply_apply, hf]
  exact hb

/-- An injective presentation computes actual degree-one cohomology as
a natural cokernel presheaf. -/
def cohomologyPresheafInjectiveCokernelIso [Injective S.X₂] :
    cokernel S.g.hom ≅ S.X₁.cohomologyPresheaf 1 := by
  let g := cohomologyPresheafBoundaryHom X S hS
  refine CategoryTheory.presheafCokernelIsoOfExact S.g.hom g ?_ ?_ ?_
  · apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro t
    exact (cohomologyPresheafSectionBoundary_eq_zero_iff X S hS V.unop
      (S.g.hom.app V t)).mpr ⟨t, rfl⟩
  · intro V s hs
    exact (cohomologyPresheafSectionBoundary_eq_zero_iff X S hS V.unop s).mp hs
  · intro V
    exact cohomologyPresheafSectionBoundary_surjective X S hS V.unop

end EtaleCohomology
