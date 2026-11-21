/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.LinearAlgebra.Isomorphisms
public import Nyll.GaloisCohomology.Topology.HomogeneousContinuousCochainsFunctor

/-!
# Restriction along a continuous group equivalence

Restriction of arbitrary continuous coefficients along a group equivalence
is injective on actual continuous cohomology.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

noncomputable section
universe u v

namespace ContinuousCohomology

variable {R : Type v} [Ring R] [TopologicalSpace R]
variable {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restricting the action by a group equivalence and its inverse gives
the original coefficients, with the identity on the coefficient group. -/
def restrictionInverseHom (e : H ≃ₜ* G) (X : TopRep.{u} R G) :
    TopRep.res e.symm.toMonoidHom (TopRep.res e.toMonoidHom X) ⟶ X := by
  refine ConcreteCategory.ofHom (C := TopRep R G)
    { toContinuousLinearMap := ContinuousLinearMap.id R X
      isIntertwining' := ?_ }
  intro g
  apply ContinuousLinearMap.ext
  intro x
  change X.ρ (e (e.symm g)) x = X.ρ g x
  rw [e.apply_symm_apply]

private theorem map_eq_id_of_identity
    (φ : G →ₜ* G) (hφ : φ = ContinuousMonoidHom.id G)
    (X : TopRep.{u} R G) (a : TopRep.res φ X ⟶ X)
    (ha : ∀ x : X, a x = x) (n : ℕ) :
    map φ a n = 𝟙 (continuousCohomology n X) := by
  subst φ
  have ha' : a = 𝟙 X := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    exact ha x
  rw [ha', map_id]

private theorem restriction_equiv_leftInverse (e : H ≃ₜ* G) (X : TopRep.{u} R G) (n : ℕ) :
    map (e : H →ₜ* G) (𝟙 (TopRep.res e.toMonoidHom X)) n ≫
      map (e.symm : G →ₜ* H) (restrictionInverseHom e X) n = 𝟙 (continuousCohomology n X) := by
  let f : H →ₜ* G := e
  let g : G →ₜ* H := e.symm
  let Y := TopRep.res e.toMonoidHom X
  let a : TopRep.res f X ⟶ Y := 𝟙 Y
  let b := restrictionInverseHom e X
  have hfg : f.comp g = ContinuousMonoidHom.id G := by
    ext x
    exact e.apply_symm_apply x
  let j : TopRep.res (f.comp g).toMonoidHom X ⟶ X := (TopRep.resFunctor g.toMonoidHom).map a ≫ b
  have hj := map_eq_id_of_identity (f.comp g) hfg X j (fun _ => rfl) n
  have hm := map_comp (X := X) (Y := Y) (Z := X) f g a b n
  exact hm.symm.trans hj

private theorem restriction_equiv_rightInverse (e : H ≃ₜ* G) (X : TopRep.{u} R G) (n : ℕ) :
    map (e.symm : G →ₜ* H) (restrictionInverseHom e X) n ≫
      map (e : H →ₜ* G) (𝟙 (TopRep.res e.toMonoidHom X)) n =
      𝟙 (continuousCohomology n (TopRep.res e.toMonoidHom X)) := by
  let f : H →ₜ* G := e
  let g : G →ₜ* H := e.symm
  let Y := TopRep.res e.toMonoidHom X
  let a : TopRep.res f X ⟶ Y := 𝟙 Y
  let b := restrictionInverseHom e X
  have hgf : g.comp f = ContinuousMonoidHom.id H := by
    ext x
    exact e.symm_apply_apply x
  let j : TopRep.res (g.comp f).toMonoidHom Y ⟶ Y := (TopRep.resFunctor f.toMonoidHom).map b ≫ a
  have hj := map_eq_id_of_identity (g.comp f) hgf Y j (fun _ => rfl) n
  have hm := map_comp (X := Y) (Y := X) (Z := Y) g f b a n
  exact hm.symm.trans hj

/-- A continuous group equivalence induces bijective restriction in every degree. -/
theorem restriction_equiv_bijective (e : H ≃ₜ* G) (X : TopRep.{u} R G) (n : ℕ) :
    Function.Bijective (map (e : H →ₜ* G) (𝟙 (TopRep.res e.toMonoidHom X)) n) := by
  let f := map (e : H →ₜ* G) (𝟙 (TopRep.res e.toMonoidHom X)) n
  let g := map (e.symm : G →ₜ* H) (restrictionInverseHom e X) n
  have hl : Function.LeftInverse g f := fun x =>
    ConcreteCategory.congr_hom (restriction_equiv_leftInverse e X n) x
  have hr : Function.RightInverse g f := fun y =>
    ConcreteCategory.congr_hom (restriction_equiv_rightInverse e X n) y
  exact ⟨hl.injective, hr.surjective⟩

/-- Restriction along a continuous group equivalence is injective on
continuous cohomology, including nontrivial coefficient actions. -/
theorem restriction_equiv_injective (e : H ≃ₜ* G)
    (X : TopRep.{u} R G) (n : ℕ) :
    Function.Injective (map (e : H →ₜ* G)
      (𝟙 (TopRep.res e.toMonoidHom X)) n) :=
  (restriction_equiv_bijective e X n).injective

/-- The cohomology map of a coefficient isomorphism is bijective. -/
theorem map_bijective_of_coeffIso {A B : TopRep.{u} R G} (i : A ≅ B) (n : ℕ) :
    Function.Bijective (map (ContinuousMonoidHom.id G) i.hom n) := by
  let F := TopRep.homogeneousContinuousCochainsFunctorOver R G ⋙ HomologicalComplex.homologyFunctor
    (TopModuleCat.{u} R) (ComplexShape.up ℕ) n
  exact ConcreteCategory.bijective_of_isIso (F.mapIso i).hom

private theorem map_groupEquiv_factor (e : H ≃ₜ* G) {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
    (j : TopRep.res e.toMonoidHom X ⟶ Y) (n : ℕ) :
    map (e : H →ₜ* G) j n = map (e : H →ₜ* G) (𝟙 (TopRep.res e.toMonoidHom X)) n ≫
      map (ContinuousMonoidHom.id H) j n := by
  let X' := TopRep.res e.toMonoidHom X
  let F : TopRep.{u} R H ⥤ TopRep.{u} R H :=
    TopRep.resFunctor (ContinuousMonoidHom.id H).toMonoidHom
  have hF : F.map (𝟙 X') = 𝟙 (F.obj X') := F.map_id X'
  have hj : F.map (𝟙 X') ≫ j = j :=
    (congrArg (fun a : F.obj X' ⟶ F.obj X' => a ≫ j) hF).trans (Category.id_comp j)
  let r := (e : H →ₜ* G).comp (ContinuousMonoidHom.id H)
  have h := map_comp (X := X) (Y := X') (Z := Y) (e : H →ₜ* G)
    (ContinuousMonoidHom.id H) (𝟙 X') j n
  exact (congrArg (fun a : TopRep.res r.toMonoidHom X ⟶ Y => map r a n) hj).symm.trans h

/-- The actual cohomology map of a continuous group equivalence and a
coefficient isomorphism is bijective in every degree. -/
theorem map_bijective_of_groupEquiv (e : H ≃ₜ* G) {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
    (i : TopRep.res e.toMonoidHom X ≅ Y) (n : ℕ) :
    Function.Bijective (map (e : H →ₜ* G) i.hom n) := by
  rw [map_groupEquiv_factor]
  exact (map_bijective_of_coeffIso i n).comp (restriction_equiv_bijective e X n)

/-- A bijective map into discrete coefficients gives an isomorphism of
the original topological representations. -/
def discreteCoefficientIsoOfBijective {A B : TopRep.{u} R G}
    [DiscreteTopology B] (f : A ⟶ B) (hf : Function.Bijective f) : A ≅ B := by
  let e := LinearEquiv.ofBijective f.hom.toContinuousLinearMap.toLinearMap hf
  have he (b : B) : f (e.symm b) = b := e.apply_symm_apply b
  let g : B ⟶ A := TopRep.ofHom
    { toContinuousLinearMap := ⟨e.symm.toLinearMap, continuous_of_discreteTopology⟩
      isIntertwining' := fun σ => by
        apply ContinuousLinearMap.ext
        intro b
        apply hf.injective
        change f (e.symm (B.ρ σ b)) = f (A.ρ σ (e.symm b))
        rw [he, TopRep.hom_comm_apply f, he] }
  refine ⟨f, g, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    exact e.symm_apply_apply a
  · apply ConcreteCategory.hom_ext
    intro b
    exact he b

end ContinuousCohomology
