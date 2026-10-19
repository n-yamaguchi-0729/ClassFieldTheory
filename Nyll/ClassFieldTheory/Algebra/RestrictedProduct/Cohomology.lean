/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Nyll.GaloisCohomology.Cyclic.MultiplicativeHilbert90

/-!
# Gluing cocycle primitives in a restricted product

Coordinate primitives define a restricted-product primitive when integral
primitives exist almost everywhere. For a finite group, a restricted-product
cocycle has all its values integral simultaneously almost everywhere. Thus
local Hilbert 90 and almost-everywhere integral Hilbert 90 imply Hilbert 90 for
the existing restricted product with its coordinatewise action.
-/

noncomputable section

open scoped RestrictedProduct

namespace RestrictedProduct.Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G ι : Type*} [Group G] {A : ι → Type*} [∀ i, CommGroup (A i)]
    {B : ∀ i, Subgroup (A i)} {𝓕 : Filter ι}
    [∀ i, MulDistribMulAction G (A i)]
    [MulDistribMulAction G (Πʳ i, [A i, B i]_[𝓕])]

/-- Evaluation sends an actual restricted-product cocycle to a coordinate cocycle. -/
theorem isMulCocycle_component
    (hsmul : ∀ (g : G) (x : Πʳ i, [A i, B i]_[𝓕]) (i : ι), (g • x) i = g • x i)
    (f : G → Πʳ i, [A i, B i]_[𝓕]) (hf : groupCohomology.IsMulCocycle₁ f) (i : ι) :
    groupCohomology.IsMulCocycle₁ (fun g => f g i) := by
  intro g h
  simpa only [RestrictedProduct.mul_apply, hsmul] using
    congrArg (fun x : Πʳ i, [A i, B i]_[𝓕] => x i) (hf g h)

/-- Choose integral coordinate primitives wherever they exist; almost-everywhere
integrality makes the resulting tuple an actual restricted-product primitive. -/
theorem isMulCoboundary_of_component_primitives
    (hsmul : ∀ (g : G) (x : Πʳ i, [A i, B i]_[𝓕]) (i : ι), (g • x) i = g • x i)
    (f : G → Πʳ i, [A i, B i]_[𝓕])
    (hlocal : ∀ i, ∃ b : A i, ∀ g : G, (g • b) / b = f g i)
    (hint : ∀ᶠ i in 𝓕, ∃ b : A i, b ∈ B i ∧ ∀ g : G, (g • b) / b = f g i) :
    groupCohomology.IsMulCoboundary₁ f := by
  classical
  let b (i : ι) : A i :=
    if h : ∃ x : A i, x ∈ B i ∧ ∀ g : G, (g • x) / x = f g i then
      Classical.choose h
    else Classical.choose (hlocal i)
  have hb (i : ι) (g : G) : (g • b i) / b i = f g i := by
    dsimp only [b]
    split_ifs with h
    · exact (Classical.choose_spec h).2 g
    · exact Classical.choose_spec (hlocal i) g
  have hbint : ∀ᶠ i in 𝓕, b i ∈ B i := by
    apply hint.mono
    intro i hi
    dsimp only [b]
    rw [dite_eq_left hi]
    exact (Classical.choose_spec hi).1
  let x : Πʳ i, [A i, B i]_[𝓕] := ⟨b, hbint⟩
  refine ⟨x, ?_⟩
  intro g
  apply RestrictedProduct.ext
  intro i
  change (g • x) i / x i = f g i
  rw [hsmul]
  exact hb i g

/-- Finite-group restricted-product Hilbert 90 follows from the actual coordinate
statements and integral solvability almost everywhere. -/
theorem isMulCoboundary_of_local_and_eventual_integral [Finite G]
    (hsmul : ∀ (g : G) (x : Πʳ i, [A i, B i]_[𝓕]) (i : ι), (g • x) i = g • x i)
    (hlocal : ∀ i (f : G → A i), groupCohomology.IsMulCocycle₁ f →
      groupCohomology.IsMulCoboundary₁ f)
    (hint : ∀ᶠ i in 𝓕, ∀ f : G → A i, groupCohomology.IsMulCocycle₁ f →
      (∀ g : G, f g ∈ B i) →
        ∃ b : A i, b ∈ B i ∧ ∀ g : G, (g • b) / b = f g)
    (f : G → Πʳ i, [A i, B i]_[𝓕]) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  have hfint : ∀ᶠ i in 𝓕, ∀ g : G, f g i ∈ B i :=
    Filter.eventually_all.mpr (fun g => (f g).2)
  apply isMulCoboundary_of_component_primitives hsmul f
  · intro i
    exact hlocal i (fun g => f g i) (isMulCocycle_component hsmul f hf i)
  · apply (hint.and hfint).mono
    intro i hi
    exact hi.1 (fun g => f g i) (isMulCocycle_component hsmul f hf i) hi.2

/-- Under the same local conditions, a cyclic norm-one restricted-product element
is an actual coboundary. -/
theorem normKernel_le_augmentationSubgroup_of_local_and_eventual_integral [Fintype G]
    (hsmul : ∀ (g : G) (x : Πʳ i, [A i, B i]_[𝓕]) (i : ι), (g • x) i = g • x i)
    (hlocal : ∀ i (f : G → A i), groupCohomology.IsMulCocycle₁ f →
      groupCohomology.IsMulCoboundary₁ f)
    (hint : ∀ᶠ i in 𝓕, ∀ f : G → A i, groupCohomology.IsMulCocycle₁ f →
      (∀ g : G, f g ∈ B i) →
        ∃ b : A i, b ∈ B i ∧ ∀ g : G, (g • b) / b = f g)
    (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    normKernelSubgroup G (Πʳ i, [A i, B i]_[𝓕]) ≤
      augmentationSubgroup G (Πʳ i, [A i, B i]_[𝓕]) σ := by
  intro a ha
  obtain ⟨f, hf, hfa⟩ := CyclicCohomology.exists_mulCocycle_of_tateNorm_eq_one σ hσ a ha
  obtain ⟨b, hb⟩ := isMulCoboundary_of_local_and_eventual_integral hsmul hlocal hint f hf
  refine ⟨b, ?_⟩
  change σ • b * b⁻¹ = a
  simpa only [div_eq_mul_inv] using (hb σ).trans hfa

end RestrictedProduct.Cohomology
