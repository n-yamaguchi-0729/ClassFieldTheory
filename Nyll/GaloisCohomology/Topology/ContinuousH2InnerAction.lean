/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives

/-!
# Inner action on actual continuous degree-two cohomology

Conjugation combined with the corresponding coefficient action right
translates the original homogeneous arguments. The two-term prism gives
an explicit continuous primitive of the difference.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopRep
open scoped Topology

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

omit [LocallyCompactSpace G] in
private theorem class_eq_zero_of_primitive (X : TopRep.{u} ℤ G) (n : ℕ)
    (w : (homogeneousCochains X).X n) (z : cocycles X (n + 1))
    (h : ((homogeneousCochains X).d n (n + 1)).hom w =
      (homogeneousCochains X).iCycles (n + 1) z) : π X (n + 1) z = 0 := by
  let C := homogeneousCochains X
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  have hinj : Function.Injective (C.iCycles (n + 1)) :=
    (ModuleCat.mono_iff_injective (F.map (C.iCycles (n + 1)))).mp inferInstance
  have hc : C.iCycles (n + 1) (C.toCycles n (n + 1) w) = (C.d n (n + 1)).hom w :=
    ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) w
  have hc' : C.toCycles n (n + 1) w = z := hinj (hc.trans h)
  rw [← hc']
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) w

private theorem innerAction_difference_class_eq_zero (X : TopRep.{u} ℤ G) (τ : G)
    (r : G →ₜ* G) (φ : TopRep.res r.toMonoidHom X ⟶ X)
    (hr : ∀ g, r g = τ⁻¹ * g * τ) (hφ : ∀ x : X, φ x = X.ρ τ x)
    (z : cocycles X 2) : π X 2 (cocyclesMap r φ 2 z - z) = 0 := by
  let C := homogeneousCochains X
  let Z (a b c : G) := (C.iCycles 2 z).val a b c
  let t : cocycles X 2 := cocyclesMap r φ 2 z
  let f := resolutionTupleHomeomorph G X 3 (C.iCycles 2 z).val
  let left (p : Fin 2 → G) : Fin 3 → G := ![p 0, p 0 * τ, p 1 * τ]
  let right (p : Fin 2 → G) : Fin 3 → G := ![p 0, p 1, p 1 * τ]
  have hl : Continuous left := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact (continuous_apply 0).mul continuous_const
    · exact (continuous_apply 1).mul continuous_const
  have hr' : Continuous right := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact (continuous_apply 1).mul continuous_const
  let p : C(Fin 2 → G, X) := ⟨fun s => f (left s) - f (right s),
    (f.continuous.comp hl).sub (f.continuous.comp hr')⟩
  have hp (s : Fin 2 → G) : p s = Z (s 0) (s 0 * τ) (s 1 * τ) - Z (s 0) (s 1) (s 1 * τ) := rfl
  have heq (g : G) (a : Fin 2 → G) : p (fun j => g * a j) = X.ρ g (p a) := by
    rw [hp, hp, map_sub]
    have h₁ : Z (g * a 0) (g * (a 0 * τ)) (g * (a 1 * τ)) =
        X.ρ g (Z (a 0) (a 0 * τ) (a 1 * τ)) :=
      (degreeTwo_equivariant X z g (a 0) (a 0 * τ) (a 1 * τ)).symm
    have h₂ : Z (g * a 0) (g * a 1) (g * (a 1 * τ)) =
        X.ρ g (Z (a 0) (a 1) (a 1 * τ)) :=
      (degreeTwo_equivariant X z g (a 0) (a 1) (a 1 * τ)).symm
    simpa only [mul_assoc] using congrArg₂ (fun x y : X => x - y) h₁ h₂
  let w := homogeneousCochainOfTuple G X 1 p heq
  have hw (a b : G) : w.val a b = Z a (a * τ) (b * τ) - Z a b (b * τ) := by
    have h := congrArg (fun q : C(Fin 2 → G, X) => q ![a, b])
      (homogeneousCochainOfTuple_apply G X 1 p heq)
    change w.val a b = p ![a, b] at h
    exact h.trans (hp ![a, b])
  have ht (a b c : G) : (C.iCycles 2 t).val a b c = Z (a * τ) (b * τ) (c * τ) := by
    change ((homogeneousCochains X).iCycles 2 (cocyclesMap r φ 2 z)).val a b c = _
    rw [mappedRelativeCocycle_apply, hφ, degreeTwo_equivariant]
    have harg (g : G) : τ * r g = g * τ := by
      rw [hr]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    change Z (τ * r a) (τ * r b) (τ * r c) = _
    simp only [harg]
  have hd : (C.d 1 2).hom w = C.iCycles 2 (t - z) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    have hsub : (C.iCycles 2 (t - z)).val a b c = (C.iCycles 2 t).val a b c - Z a b c :=
      congrArg (fun f : C.X 2 => f.val a b c) (map_sub (C.iCycles 2).hom t z)
    change (((homogeneousCochains X).d 1 2).hom w).val a b c = _
    rw [congrArg (fun f => f a b c) (homogeneousCochains.d_apply X 1 w), hsub, ht]
    change w.val b c - (w.val a c - w.val a b) = _
    simp only [hw]
    let E₁ := Z b (b * τ) (c * τ) - Z a (b * τ) (c * τ) +
      Z a b (c * τ) - Z a b (b * τ)
    let E₂ := Z b c (c * τ) - Z a c (c * τ) + Z a b (c * τ) - Z a b c
    let E₃ := Z (a * τ) (b * τ) (c * τ) - Z a (b * τ) (c * τ) +
      Z a (a * τ) (c * τ) - Z a (a * τ) (b * τ)
    have h₁ : E₁ = 0 := degreeTwo_cocycle_equation X z a b (b * τ) (c * τ)
    have h₂ : E₂ = 0 := degreeTwo_cocycle_equation X z a b c (c * τ)
    have h₃ : E₃ = 0 := degreeTwo_cocycle_equation X z a (a * τ) (b * τ) (c * τ)
    calc
      _ = E₁ - E₂ - E₃ + (Z (a * τ) (b * τ) (c * τ) - Z a b c) := by
        dsimp only [E₁, E₂, E₃]
        abel
      _ = _ := by rw [h₁, h₂, h₃, sub_self, sub_zero, zero_add]
  exact class_eq_zero_of_primitive X 1 w (t - z) hd

/-- Inner conjugation with its original coefficient action acts trivially in degree two. -/
theorem map_inner_eq_id_two (X : TopRep.{u} ℤ G) (τ : G)
    (r : G →ₜ* G) (φ : TopRep.res r.toMonoidHom X ⟶ X)
    (hr : ∀ g, r g = τ⁻¹ * g * τ) (hφ : ∀ x : X, φ x = X.ρ τ x) :
    ContinuousCohomology.map r φ 2 = 𝟙 (continuousCohomology 2 X) := by
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  have hclass : (ContinuousCohomology.map r φ 2) (π X 2 z) = π X 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  change (ContinuousCohomology.map r φ 2) (π X 2 z) = π X 2 z
  rw [hclass]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact innerAction_difference_class_eq_zero X τ r φ hr hφ z

end ContinuousCohomology
