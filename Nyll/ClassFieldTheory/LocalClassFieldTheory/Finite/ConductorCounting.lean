/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.Different.Hilbert
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! # Character counting in the lower ramification filtration -/

@[expose] public section

open scoped IsMulCommutative
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.HilbertRamification.Higher

namespace LocalClassFieldTheory

universe u v w x

open scoped Classical in
/-- Summing a subgroup's order over characters nontrivial on it gives the group order
times the subgroup order minus one. -/
theorem finsum_character_ramificationLayerWeight
    (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] (H : Subgroup G) :
    (∑ᶠ χ : G →* Mˣ, (if H ≤ χ.ker then 0 else Nat.card H)) =
      Nat.card G * (Nat.card H - 1) := by
  classical
  let : Fintype (G →* Mˣ) := Fintype.ofFinite _
  let A := (MonoidHom.domRestrictHom H Mˣ).ker
  have hA (χ : G →* Mˣ) : χ ∈ A ↔ H ≤ χ.ker := by
    change MonoidHom.domRestrictHom H Mˣ χ = 1 ↔ H ≤ χ.ker
    constructor
    · intro h x hx
      exact DFunLike.congr_fun h ⟨x, hx⟩
    · intro h
      apply MonoidHom.ext
      intro x
      exact h x.2
  have hterm (χ : G →* Mˣ) : (if H ≤ χ.ker then 0 else Nat.card H) =
      if χ ∉ A then Nat.card H else 0 := by
    by_cases h : χ ∈ A
    · rw [ite_eq_left ((hA χ).mp h), ite_eq_right (not_not.mpr h)]
    · rw [ite_eq_right (fun hk => h ((hA χ).mpr hk)), ite_eq_left h]
  let s := Finset.univ.filter (fun χ : G →* Mˣ => χ ∉ A)
  have hs : s.card = Nat.card (G →* Mˣ) - Nat.card A := by
    calc
      s.card = Fintype.card {χ : G →* Mˣ // χ ∉ A} := (Fintype.card_subtype _).symm
      _ = Nat.card (G →* Mˣ) - Nat.card A := by
        rw [Fintype.card_subtype_compl]
        simp only [Nat.card_eq_fintype_card]
  calc
    (∑ᶠ χ : G →* Mˣ, (if H ≤ χ.ker then 0 else Nat.card H)) = s.card * Nat.card H := by
      rw [finsum_eq_sum_of_fintype]
      simp_rw [hterm]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl
    _ = (Nat.card G - Nat.card (G ⧸ H)) * Nat.card H := by
      rw [hs, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M,
        CommGroup.card_domRestrictHom_ker M H]
    _ = Nat.card G * (Nat.card H - 1) := by
      have hcard := H.card_eq_card_quotient_mul_card_subgroup
      rw [Nat.sub_mul, ← hcard, Nat.mul_sub_one]

open scoped Classical in
/-- For a finite local abelian extension, weighted character contributions to the
lower filtration sum to the group order times the actual different exponent. -/
theorem exists_differentIdeal_eq_pow_and_finsum_character_ramificationWeight
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsScalarTower base.valuationSubring K L]
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base.toDVF target.toDVF)
    (M : Type*) [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))] :
    ∃ N d : ℕ,
      RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
          base target = target.maximalIdeal ^ d ∧
      (∑ᶠ χ : Gal(L/K) →* Mˣ, ∑ n ∈ Finset.range N,
        if lowerRamificationGroup (base := base.toDVF) (target := target.toDVF)
            huniq (n : ℝ) ≤ χ.ker then 0 else
          Nat.card (lowerRamificationGroup (base := base.toDVF) (target := target.toDVF)
            huniq (n : ℝ))) = Nat.card (Gal(L/K)) * d := by
  classical
  let : Fintype (Gal(L/K) →* Mˣ) := Fintype.ofFinite _
  obtain ⟨N, _, hd⟩ :=
    exists_differentIdeal_eq_maximalIdeal_pow_lowerRamificationSum base target huniq
  let G : ℕ → Subgroup (Gal(L/K)) := fun n =>
    lowerRamificationGroup (base := base.toDVF) (target := target.toDVF) huniq (n : ℝ)
  refine ⟨N, ∑ n ∈ Finset.range N, (Nat.card (G n) - 1), hd, ?_⟩
  change (∑ᶠ χ : Gal(L/K) →* Mˣ, ∑ n ∈ Finset.range N,
    if G n ≤ χ.ker then 0 else Nat.card (G n)) =
      Nat.card (Gal(L/K)) * ∑ n ∈ Finset.range N, (Nat.card (G n) - 1)
  rw [finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← finsum_eq_sum_of_fintype]
  exact finsum_character_ramificationLayerWeight (Gal(L/K)) M (G n)

end LocalClassFieldTheory
