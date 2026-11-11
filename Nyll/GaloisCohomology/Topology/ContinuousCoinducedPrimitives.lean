/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousTupleExactness
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Explicit continuous primitives for coinduced coefficients

Insertion of the evaluation coordinate contracts positive homogeneous
continuous cocycles with actual coinduced coefficients. This is the
acyclicity needed for continuous dimension shifting.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (X : TopRep.{u} ℤ G)

/-- Inserting the evaluation coordinate defines a continuous lower tuple. -/
def coinducedTuplePrimitive (n : ℕ)
    (f : C(Fin (n + 2) → G, X.coind₁)) :
    C(Fin (n + 1) → G, X.coind₁) :=
  Homeomorph.curry
    (⟨fun ax => f (Fin.cons (α := fun _ : Fin (n + 2) => G) ax.2 ax.1) ax.2, by
      have ht : Continuous (fun ax : (Fin (n + 1) → G) × G =>
          Fin.cons (α := fun _ : Fin (n + 2) => G) ax.2 ax.1) :=
        (finiteTupleConsHomeomorph G (n + 1)).continuous.comp
          (continuous_snd.prodMk continuous_fst)
      exact continuous_eval.comp
        ((f.continuous.comp ht).prodMk continuous_snd)⟩ :
      C((Fin (n + 1) → G) × G, X))

/-- The primitive is literally evaluation after insertion. -/
theorem coinducedTuplePrimitive_apply (n : ℕ)
    (f : C(Fin (n + 2) → G, X.coind₁))
    (a : Fin (n + 1) → G) (x : G) :
    coinducedTuplePrimitive G X n f a x =
      f (Fin.cons (α := fun _ : Fin (n + 2) => G) x a) x := rfl

/-- Insertion of the evaluation coordinate preserves actual equivariance. -/
theorem coinducedTuplePrimitive_equivariant (n : ℕ)
    (f : C(Fin (n + 2) → G, X.coind₁))
    (hf : ∀ (σ : G) (a : Fin (n + 2) → G),
      f (fun i => σ * a i) = X.coind₁.ρ σ (f a))
    (σ : G) (a : Fin (n + 1) → G) :
    coinducedTuplePrimitive G X n f (fun i => σ * a i) =
      X.coind₁.ρ σ (coinducedTuplePrimitive G X n f a) := by
  apply ContinuousMap.ext
  intro x
  have ht :
      (fun i => σ * Fin.cons (α := fun _ : Fin (n + 2) => G) (σ⁻¹ * x) a i) =
        Fin.cons (α := fun _ : Fin (n + 2) => G) x (fun i => σ * a i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact mul_inv_cancel_left σ x
    · rfl
  have h := congrArg (fun h : C(G, X) => h x)
    (hf σ (Fin.cons (α := fun _ : Fin (n + 2) => G) (σ⁻¹ * x) a))
  rw [ht] at h
  exact h

/-- The explicit inserted tuple is a primitive of every positive cocycle. -/
theorem coinducedTuplePrimitive_boundary (n : ℕ)
    (f : C(Fin (n + 2) → G, X.coind₁))
    (hc : ∀ a : Fin (n + 3) → G,
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        f (fun j => a (i.succAbove j)) = 0)
    (a : Fin (n + 2) → G) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      coinducedTuplePrimitive G X n f (fun j => a (i.succAbove j))) = f a := by
  apply ContinuousMap.ext
  intro x
  have h := congrArg (fun h : C(G, X) => h x)
    (hc (Fin.cons (α := fun _ : Fin (n + 3) => G) x a))
  rw [Fin.sum_univ_succ] at h
  have hface (i : Fin (n + 2)) :
      (fun j =>
        Fin.cons (α := fun _ : Fin (n + 3) => G) x a (i.succ.succAbove j)) =
        Fin.cons (α := fun _ : Fin (n + 2) => G) x
          (fun j => a (i.succAbove j)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Fin.succ_succAbove_zero]
      rfl
    · rw [Fin.succ_succAbove_succ]
      rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.zero_succAbove,
    Fin.cons_succ, Fin.val_succ, hface, pow_succ, mul_neg_one, neg_smul] at h
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  have h' : f a x - (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      f (Fin.cons (α := fun _ : Fin (n + 2) => G) x
        (fun j => a (i.succAbove j))) x) = 0 := by
    simpa only [ContinuousMap.add_apply, ContinuousMap.sum_apply,
      ContinuousMap.neg_apply, ContinuousMap.smul_apply,
      ContinuousMap.zero_apply, Finset.sum_neg_distrib, sub_eq_add_neg] using h
  exact (sub_eq_zero.mp h').symm

/-- Actual coinduced coefficients have explicit positive-degree cochain primitives. -/
theorem exists_coinduced_homogeneousCochain_primitive (n : ℕ)
    (z : (homogeneousCochains X.coind₁).X (n + 1))
    (hz : (homogeneousCochains X.coind₁).d (n + 1) (n + 2) z = 0) :
    ∃ b : (homogeneousCochains X.coind₁).X n,
      (homogeneousCochains X.coind₁).d n (n + 1) b = z :=
  exists_homogeneousCochain_primitive_of_tuple_primitives G X.coind₁ n
    (fun f hf hc => ⟨coinducedTuplePrimitive G X n f,
      coinducedTuplePrimitive_equivariant G X n f hf,
      coinducedTuplePrimitive_boundary G X n f hc⟩) z hz

/-- All positive actual continuous cohomology groups of coinduced coefficients vanish. -/
theorem continuousCohomology_coinduced_eq_zero (n : ℕ)
    (a : continuousCohomology (n + 1) X.coind₁) : a = 0 :=
  continuousCohomology_eq_zero_of_cochain_primitives G X.coind₁ n
    (exists_coinduced_homogeneousCochain_primitive G X n) a

omit [LocallyCompactSpace G] in
/-- The actual coinduced function space is discrete for compact groups
and discrete coefficients. -/
theorem coinduced_discreteTopology [CompactSpace G] [DiscreteTopology X] :
    DiscreteTopology X.coind₁ := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hs : {f : C(G, X) | Set.range f ⊆ ({0} : Set X)} =
      ({0} : Set C(G, X)) := by
    ext f
    constructor
    · intro hf
      apply Set.mem_singleton_iff.mpr
      apply ContinuousMap.ext
      intro x
      exact Set.mem_singleton_iff.mp (hf (Set.mem_range_self x))
    · rintro rfl
      rintro y ⟨x, rfl⟩
      rfl
  rw [← hs]
  exact ContinuousMap.isOpen_setOfPred_range_subset (isOpen_discrete _)

/-- A jointly continuous coefficient action induces a jointly continuous
action on actual coinduced coefficients. -/
theorem coinduced_action_continuous
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    Continuous (fun gf : G × X.coind₁ => X.coind₁.ρ gf.1 gf.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hg : Continuous (fun t : (G × C(G, X)) × G => t.1.1) :=
    continuous_fst.fst
  have hf : Continuous (fun t : (G × C(G, X)) × G => t.1.2) :=
    continuous_fst.snd
  have hv : Continuous (fun t : (G × C(G, X)) × G => t.1.2 (t.1.1⁻¹ * t.2)) :=
    continuous_eval.comp (hf.prodMk (hg.inv.mul continuous_snd))
  exact hX.comp (hg.prodMk hv)

end TopRep
