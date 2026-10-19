/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.Herbrand.Product
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness

/-!
# Products with only finitely many nontrivial Tate factors

Low-degree Tate cohomology commutes with arbitrary products. If all but finitely
many factors vanish, restriction to the exceptional set computes both finite
Tate groups and the Herbrand quotient. This applies to products of local units.
-/

noncomputable section

namespace CyclicCohomology

open ProfiniteCohomology.Herbrand

private def piTrivialOutsideEquiv {ι : Type*} (B : ι → Type*) [∀ i, Group (B i)]
    (S : Finset ι) (h : ∀ i, i ∉ S → Subsingleton (B i)) :
    (∀ i, B i) ≃ (∀ i : S, B i.val) := by
  classical
  exact
    { toFun := fun f i => f i.val
      invFun := fun f i => if hi : i ∈ S then f ⟨i, hi⟩ else 1
      left_inv := fun f => by
        funext i
        change (if hi : i ∈ S then f i else 1) = f i
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceDIte]
        · simp only [hi, ↓reduceDIte]
          have : Subsingleton (B i) := h i hi
          exact Subsingleton.elim _ _
      right_inv := fun f => by
        funext i
        change (if hi : i.val ∈ S then f ⟨i.val, hi⟩ else 1) = f i
        simp only [i.2, ↓reduceDIte] }

variable {G ι : Type*} [Group G] [Fintype G] (A : ι → Type*)
    [∀ i, CommGroup (A i)] [∀ i, MulDistribMulAction G (A i)]

local instance : MulDistribMulAction G (∀ i, A i) := piMulDistribMulAction G A

/-- An arbitrary product with trivial Tate factors outside `S` has the finite product quotient. -/
theorem herbrandQuotient_pi_of_subsingleton_off_finset (S : Finset ι) (σ : G)
    [∀ i, Finite (HerbrandH0 G (A i))]
    [∀ i, Finite (HerbrandHMinusOne G (A i) σ)]
    (h0 : ∀ i, i ∉ S → Subsingleton (HerbrandH0 G (A i)))
    (hm : ∀ i, i ∉ S → Subsingleton (HerbrandHMinusOne G (A i) σ)) :
    ∃ hP : HerbrandQuotientDefined G (∀ i, A i) σ,
      let _ : Finite (HerbrandH0 G (∀ i, A i)) := hP.1
      let _ : Finite (HerbrandHMinusOne G (∀ i, A i) σ) := hP.2
      herbrandQuotient (G := G) (A := ∀ i, A i) σ =
        ∏ i : S, herbrandQuotient (G := G) (A := A i.val) σ := by
  let e0 := (herbrandH0PiEquiv (G := G) A).toEquiv.trans
    (piTrivialOutsideEquiv (fun i => HerbrandH0 G (A i)) S h0)
  let em := (herbrandHMinusOnePiEquiv (G := G) A σ).toEquiv.trans
    (piTrivialOutsideEquiv (fun i => HerbrandHMinusOne G (A i) σ) S hm)
  have hP : HerbrandQuotientDefined G (∀ i, A i) σ :=
    ⟨Finite.of_equiv _ e0.symm, Finite.of_equiv _ em.symm⟩
  refine ⟨hP, ?_⟩
  intro hP0 hPm
  rw [herbrandQuotient_eq_card_ratio, Nat.card_congr e0, Nat.card_congr em,
    Nat.card_pi, Nat.card_pi, Nat.cast_prod, Nat.cast_prod]
  simp only [herbrandQuotient_eq_card_ratio]
  exact (Finset.prod_div_distrib _ _).symm

/-- If every local quotient is one, so is the product with only finitely many nontrivial factors. -/
theorem herbrandQuotient_pi_eq_one_of_subsingleton_off_finset (S : Finset ι) (σ : G)
    [∀ i, Finite (HerbrandH0 G (A i))]
    [∀ i, Finite (HerbrandHMinusOne G (A i) σ)]
    (h0 : ∀ i, i ∉ S → Subsingleton (HerbrandH0 G (A i)))
    (hm : ∀ i, i ∉ S → Subsingleton (HerbrandHMinusOne G (A i) σ))
    (hQ : ∀ i : S, herbrandQuotient (G := G) (A := A i.val) σ = 1) :
    ∃ hP : HerbrandQuotientDefined G (∀ i, A i) σ,
      let _ : Finite (HerbrandH0 G (∀ i, A i)) := hP.1
      let _ : Finite (HerbrandHMinusOne G (∀ i, A i) σ) := hP.2
      herbrandQuotient (G := G) (A := ∀ i, A i) σ = 1 := by
  obtain ⟨hP, h⟩ := herbrandQuotient_pi_of_subsingleton_off_finset A S σ h0 hm
  refine ⟨hP, ?_⟩
  intro hP0 hPm
  exact h.trans (Finset.prod_eq_one fun i _ => hQ i)

end CyclicCohomology
