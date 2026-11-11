/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

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

private def restrictionInverseHom (e : H ≃ₜ* G) (X : TopRep.{u} R G) :
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

/-- Restriction along a continuous group equivalence is injective on
continuous cohomology, including nontrivial coefficient actions. -/
theorem restriction_equiv_injective (e : H ≃ₜ* G)
    (X : TopRep.{u} R G) (n : ℕ) :
    Function.Injective (map (e : H →ₜ* G)
      (𝟙 (TopRep.res e.toMonoidHom X)) n) := by
  let f : H →ₜ* G := e
  let g : G →ₜ* H := e.symm
  let Y := TopRep.res e.toMonoidHom X
  let a : TopRep.res f X ⟶ Y := 𝟙 Y
  let b := restrictionInverseHom e X
  have hfg : f.comp g = ContinuousMonoidHom.id G := by
    ext x
    exact e.apply_symm_apply x
  have hc : map f a n ≫ map g b n = 𝟙 (continuousCohomology n X) := by
    exact (map_comp f g a b n).symm.trans
      (map_eq_id_of_identity (f.comp g) hfg X
        ((TopRep.resFunctor (g : G →* H)).map a ≫ b) (fun _ => rfl) n)
  intro x y hxy
  have hx := ConcreteCategory.congr_hom hc x
  have hy := ConcreteCategory.congr_hom hc y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hx hy
  exact hx.symm.trans ((congrArg (fun z => map g b n z) hxy).trans hy)

end ContinuousCohomology
