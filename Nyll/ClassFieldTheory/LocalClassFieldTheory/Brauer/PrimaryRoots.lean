/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Nyll.ClassFieldTheory.Algebra.LocalField.PrincipalUnitTopology
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity

/-! # A uniform bound on primary roots of unity of a local field -/

@[expose] public section

open scoped ValuativeRel
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace LocalFieldTheory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (p : ℕ) [Fact p.Prime]

/-- Primary roots inject into an actual finite quotient of valuation-ring
units. A deep principal subgroup avoids the finitely many nontrivial
p-th roots, so it contains no nontrivial p-primary root. -/
theorem finite_localPrimaryRoots : Finite (CommGroup.primaryComponent Kˣ p) := by
  let : T2Space K := localFieldT2Space K
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let S : Set Kˣ := (rootsOfUnity p K : Set Kˣ) \ {1}
  let : Finite (rootsOfUnity p K) := inferInstanceAs (Finite (rootsOfUnity p K))
  have hSfin : S.Finite := (Set.toFinite (rootsOfUnity p K : Set Kˣ)).subset (fun _ h => h.1)
  have hOne : (1 : Kˣ) ∈ Sᶜ := fun h => h.2 (Set.mem_singleton _)
  obtain ⟨depth, _, hdepth⟩ := exists_fieldPrincipalUnits_subset_of_mem_nhds K Sᶜ
    (hSfin.isClosed.isOpen_compl.mem_nhds hOne)
  let V := fieldPrincipalUnits K depth
  let U := localBaseUnitSubgroup K
  let W := V.subgroupOf U
  have hU : IsCompact (U : Set Kˣ) := isCompact_range (integerUnitsToFieldUnits_continuous K)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hW : IsOpen (W : Set U) :=
    (isOpen_fieldPrincipalUnits K depth).preimage continuous_subtype_val
  let : Finite (U ⧸ W) := Subgroup.quotient_finite_of_isOpen W hW
  let P := CommGroup.primaryComponent Kˣ p
  have hPU : P ≤ U := by
    intro x hx
    obtain ⟨m, hm⟩ := CommGroup.mem_primaryComponent.mp hx
    apply (mem_localBaseUnitSubgroup_iff_valuation_eq_one K x).mpr
    have hval := congrArg (fun u : Kˣ => ValuativeRel.valuation K (u : K)) hm
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at hval
    exact (pow_eq_one_iff_of_nonneg zero_le (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp hval
  let f : P →* U ⧸ W := (QuotientGroup.mk' W).comp (Subgroup.inclusion hPU)
  have hV : ∀ (x : Kˣ), x ∈ V → ∀ m : ℕ, x ^ (p ^ m) = 1 → x = 1 := by
    intro x hx m
    induction m with
    | zero =>
      intro hm
      rwa [pow_zero, pow_one] at hm
    | succ m ih =>
      intro hm
      apply ih
      by_contra hn
      have hxpow : (x ^ (p ^ m)) ^ p = 1 := by rwa [← pow_mul, ← pow_succ]
      exact hdepth (V.pow_mem hx _) ⟨hxpow, fun h => hn (Set.mem_singleton_iff.mp h)⟩
  apply Finite.of_injective f
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  have hxV : (x : Kˣ) ∈ V :=
    (QuotientGroup.eq_one_iff (Subgroup.inclusion hPU x)).mp hx
  obtain ⟨m, hm⟩ := CommGroup.mem_primaryComponent.mp x.property
  exact Subtype.ext (hV x.val hxV m hm)

/-- A single p-power kills the p-primary roots of unity, uniformly in the
exponent used to display a root. -/
theorem exists_pow_annihilating_localPrimaryRoots :
    ∃ m : ℕ, ∀ (k : ℕ) (a : Kˣ), a ^ (p ^ k) = 1 → a ^ (p ^ m) = 1 := by
  let P := CommGroup.primaryComponent Kˣ p
  let : Finite P := finite_localPrimaryRoots K p
  have hP : IsPGroup p P := by
    intro x
    obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp x.property
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  refine ⟨m, fun k a ha => ?_⟩
  let x : P := ⟨a, CommGroup.mem_primaryComponent.mpr ⟨k, ha⟩⟩
  rw [← hm]
  exact congrArg Subtype.val (pow_card_eq_one' (x := x))

end LocalFieldTheory
