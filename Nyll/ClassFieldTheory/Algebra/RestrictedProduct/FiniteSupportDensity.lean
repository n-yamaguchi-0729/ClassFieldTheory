/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Finite local products detect continuous maps on a restricted product

Truncation converges inside the single principal-filter chart containing
the given restricted family. Thus finite products of actual one-place
inclusions detect every continuous homomorphism into a Hausdorff group.
-/

@[expose] public section

noncomputable section

open scoped RestrictedProduct
open Filter Topology

namespace RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ i, CommGroup (G i)]
  [∀ i, TopologicalSpace (G i)] (A : ∀ i, Subgroup (G i))

/-- Keep the given components at a finite set and use the identity elsewhere. -/
def finiteTruncation (x : Πʳ i, [G i, A i]) (s : Finset ι) :
    Πʳ i, [G i, A i] := by
  classical
  exact ⟨fun i => if i ∈ s then x i else 1,
    s.eventually_cofinite_notMem.mono fun i hi => by
      change (if i ∈ s then x i else 1) ∈ A i
      rw [ite_eq_right hi]
      exact (A i).one_mem⟩

omit [∀ i, TopologicalSpace (G i)] in
open scoped Classical in
/-- Each truncation is the literal product of its one-place inclusions. -/
theorem finiteTruncation_eq_prod (x : Πʳ i, [G i, A i]) (s : Finset ι) :
    finiteTruncation A x s = ∏ i ∈ s, mulSingle A i (x i) := by
  apply RestrictedProduct.ext
  intro i
  change (if i ∈ s then x i else 1) =
    evalMonoidHom G i (∏ j ∈ s, mulSingle A j (x j))
  rw [map_prod]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, Finset.prod_eq_single i]
    · exact (mulSingle_eq_same A i (x i)).symm
    · intro j hj hji
      exact mulSingle_eq_of_ne A (x j) hji.symm
    · exact fun h => (h hi).elim
  · rw [ite_eq_right hi]
    symm
    apply Finset.prod_eq_one
    intro j hj
    exact mulSingle_eq_of_ne A (x j) (fun h => hi (h.symm ▸ hj))

/-- Finite truncations converge in the actual restricted-product topology. -/
theorem tendsto_finiteTruncation (x : Πʳ i, [G i, A i]) :
    Tendsto (finiteTruncation A x) atTop (𝓝 x) := by
  classical
  let S : Set ι := {i | x i ∈ A i}
  have hS : Filter.cofinite ≤ Filter.principal S :=
    Filter.le_principal_iff.mpr x.property
  let y : Πʳ i, [G i, A i]_[Filter.principal S] := ⟨x, fun i hi => hi⟩
  let t (s : Finset ι) : Πʳ i, [G i, A i]_[Filter.principal S] :=
    ⟨fun i => if i ∈ s then x i else 1, fun i hi => by
      change (if i ∈ s then x i else 1) ∈ A i
      by_cases his : i ∈ s
      · rw [ite_eq_left his]
        exact hi
      · rw [ite_eq_right his]
        exact (A i).one_mem⟩
  have ht : Tendsto t atTop (𝓝 y) := by
    apply isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with s hs
    change x i = if i ∈ s then x i else 1
    exact (ite_eq_left (hs (Finset.mem_singleton_self i))).symm
  exact (continuous_inclusion hS).continuousAt.tendsto.comp ht

open scoped Classical in
/-- Actual local inclusions determine every continuous homomorphism. -/
theorem continuousMonoidHom_ext_mulSingle
    {B : Type*} [CommGroup B] [TopologicalSpace B] [T2Space B]
    (f g : (Πʳ i, [G i, A i]) →ₜ* B)
    (h : ∀ i (u : G i), f (mulSingle A i u) = g (mulSingle A i u)) : f = g := by
  classical
  apply DFunLike.ext
  intro x
  have hp (s : Finset ι) : f (finiteTruncation A x s) = g (finiteTruncation A x s) := by
    rw [finiteTruncation_eq_prod, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact h i (x i)
  have hf := f.continuous_toFun.continuousAt.tendsto.comp (tendsto_finiteTruncation A x)
  have hg := g.continuous_toFun.continuousAt.tendsto.comp (tendsto_finiteTruncation A x)
  have hfg : (fun s => f (finiteTruncation A x s)) =
      (fun s => g (finiteTruncation A x s)) := funext hp
  change Tendsto (fun s => f (finiteTruncation A x s)) atTop (𝓝 (f x)) at hf
  rw [hfg] at hf
  exact tendsto_nhds_unique hf hg

end RestrictedProduct
