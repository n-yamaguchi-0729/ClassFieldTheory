/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.Different
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
import Nyll.ValuedFieldTheory.Ramification.Different.GaloisPolynomial
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Conductor

/-! # Hilbert's different exponent as a sum over the nonidentity automorphisms -/

@[expose] public section

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.DiscreteValuationField.ValuedExtension
open IsDiscreteValuationRing Polynomial

namespace RamificationTheory.HilbertRamification.Higher

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
  [base.valuation.HasExtension target.valuation]
  [IsScalarTower base.valuationSubring target.valuationSubring L]
  [IsScalarTower base.valuationSubring K L]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem adjoin_field_eq_top_of_adjoin_valuationSubring_eq_top
    (z : target.valuationSubring) (hz : Algebra.adjoin base.valuationSubring {z} = ⊤) :
    IntermediateField.adjoin K {algebraMap target.valuationSubring L z} = ⊤ := by
  let E := IntermediateField.adjoin K {algebraMap target.valuationSubring L z}
  have hzE : algebraMap target.valuationSubring L z ∈ E :=
    IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  have hle : Algebra.adjoin base.valuationSubring {z} ≤
      (E.toSubalgebra.restrictScalars base.valuationSubring).comap
        (IsScalarTower.toAlgHom base.valuationSubring target.valuationSubring L) := by
    apply Algebra.adjoin_le
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ha.symm ▸ hzE
  rw [hz] at hle
  apply top_unique
  intro y _
  let : IsFractionRing target.valuationSubring L := target.toDVF.valuationSubring_isFractionRing
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := target.valuationSubring) y
  exact E.div_mem (hle Algebra.mem_top) (hle Algebra.mem_top)

private theorem addVal_finset_product {R ι : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, addVal_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

private theorem span_singleton_eq_pow_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha : a ≠ 0) :
    Ideal.span ({a} : Set R) = IsLocalRing.maximalIdeal R ^ (addVal R a).toNat := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨d, e, he⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [he, addVal_mul, addVal_eq_zero_of_unit, zero_add, hπ.addVal_pow, ENat.toNat_natCast,
    ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr e.isUnit,
    Ideal.top_mul, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

open scoped Classical in
/-- The different of a finite local Galois extension is the maximal ideal raised to the sum of
the canonical ramification numbers of its nonidentity automorphisms. -/
theorem differentIdeal_eq_maximalIdeal_pow_sum_ramificationNumbers
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base.toDVF target.toDVF) :
    RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target = target.maximalIdeal ^
      ∑ σ ∈ Finset.univ.erase (1 : Gal(L/K)),
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF) huniq σ).toNat := by
  classical
  let R := target.valuationSubring
  let : IsDiscreteValuationRing R := target.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing R L := target.toDVF.valuationSubring_isFractionRing
  let : IsFractionRing base.valuationSubring K := base.toDVF.valuationSubring_isFractionRing
  let : Module.Finite base.valuationSubring R :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let z : R := chosenRamificationGeneratorOfUniqueExtension
    (base := base.toDVF) (target := target.toDVF) huniq
  have hz : Algebra.adjoin base.valuationSubring ({z} : Set R) = ⊤ :=
    chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
      (base := base.toDVF) (target := target.toDVF) huniq
  have hzL := adjoin_field_eq_top_of_adjoin_valuationSubring_eq_top base target z hz
  have hzA : Algebra.adjoin K {algebraMap R L z} = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic fun y _ => IsAlgebraic.of_finite K y).mp hzL
  let d : R := aeval z (derivative (minpoly base.valuationSubring z))
  have hd := conductor_mul_differentIdealOfFiniteSeparable_eq_span_derivative base target z hzA
  rw [conductor_eq_top_of_adjoin_eq_top hz, Ideal.top_mul] at hd
  change _ = Ideal.span ({d} : Set R) at hd
  let s := Finset.univ.erase (1 : Gal(L/K))
  let displacement (σ : Gal(L/K)) : R :=
    valuationSubringAutOfUniqueExtension (base := base.toDVF) (target := target.toDVF) huniq σ z - z
  have hd0 : d ≠ 0 := by
    intro h
    exact (differentIdealOfFiniteSeparable_ne_bot base target) (by
        rw [hd, h, Ideal.span_singleton_eq_bot])
  have hprod : d = ∏ σ ∈ s, -(displacement σ) := by
    apply IsFractionRing.injective R L
    have hint : IsIntegral base.valuationSubring z := IsIntegral.of_finite _ z
    have hdMap : algebraMap R L d = aeval (algebraMap R L z)
        (derivative (minpoly K (algebraMap R L z))) := by
      let f : R →ₐ[base.valuationSubring] L :=
        IsScalarTower.toAlgHom base.valuationSubring R L
      calc
        algebraMap R L d =
            aeval (algebraMap R L z) (derivative (minpoly base.valuationSubring z)) :=
          (aeval_algHom_apply f z (derivative (minpoly base.valuationSubring z))).symm
        _ = _ := by rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hint,
          derivative_map, aeval_map_algebraMap]
    rw [hdMap, aeval_derivative_minpoly_eq_prod_galois_displacements hzL, map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    rw [map_neg, map_sub, neg_sub]
    rfl
  have hsum : addVal R d = ((∑ σ ∈ s, (intrinsicRamificationNumberOfUniqueExtension
      (base := base.toDVF) (target := target.toDVF) huniq σ).toNat : ℕ) : ℕ∞) := by
    rw [hprod, addVal_finset_product, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hs1 : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    have htop : ramificationNumberOfUniqueExtension
        (base := base.toDVF) (target := target.toDVF) huniq z σ ≠ ⊤ :=
      (ramificationNumberOfUniqueExtension_eq_top_iff huniq hz σ).not.mpr hs1
    have hneg : addVal R (-(displacement σ)) = addVal R (displacement σ) := by
      rw [← neg_one_mul, addVal_mul, addVal_eq_zero_iff.mpr (isUnit_one.neg), zero_add]
    rw [hneg]
    exact (ENat.natCast_toNat htop).symm
  rw [hd, span_singleton_eq_pow_addVal hd0, hsum, ENat.toNat_natCast]

open scoped Classical in
/-- Hilbert's different formula with a finite cutoff beyond which all lower groups are trivial. -/
theorem exists_differentIdeal_eq_maximalIdeal_pow_lowerRamificationSum
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base.toDVF target.toDVF) :
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → lowerRamificationGroup
        (base := base.toDVF) (target := target.toDVF) huniq (n : ℝ) = ⊥) ∧
      RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
          base target = target.maximalIdeal ^
        ∑ n ∈ Finset.range N, (Nat.card (lowerRamificationGroup
          (base := base.toDVF) (target := target.toDVF) huniq (n : ℝ)) - 1) := by
  classical
  let s := Finset.univ.erase (1 : Gal(L/K))
  let i := intrinsicRamificationNumberOfUniqueExtension
    (base := base.toDVF) (target := target.toDVF) huniq
  let d : Gal(L/K) → ℕ := fun σ => (i σ).toNat
  let G : ℕ → Subgroup (Gal(L/K)) :=
    fun n => lowerRamificationGroup (base := base.toDVF) (target := target.toDVF) huniq (n : ℝ)
  let N := s.sup d
  let z := chosenRamificationGeneratorOfUniqueExtension
    (base := base.toDVF) (target := target.toDVF) huniq
  have hz : Algebra.adjoin base.valuationSubring ({z} : Set target.valuationSubring) = ⊤ :=
    chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
      (base := base.toDVF) (target := target.toDVF) huniq
  have hdepth (σ : Gal(L/K)) (hσ : σ ∈ s) (n : ℕ) : σ ∈ G n ↔ n < d σ := by
    have hfinite : i σ ≠ ⊤ :=
      (ramificationNumberOfUniqueExtension_eq_top_iff huniq hz σ).not.mpr
        (Finset.mem_erase.mp hσ).1
    change σ ∈ lowerRamificationGroup (base := base.toDVF) (target := target.toDVF)
      huniq (n : ℝ) ↔ _
    rw [mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge]
    change ((n + 1 : ℕ) : ℕ∞) ≤ i σ ↔ n < d σ
    rw [← ENat.natCast_toNat hfinite, ENat.natCast_le_natCast, Nat.succ_le_iff]
  have hbound (σ : Gal(L/K)) (hσ : σ ∈ s) : d σ ≤ N := Finset.le_sup hσ
  have hbot (n : ℕ) (hn : N ≤ n) : G n = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    apply Subgroup.mem_bot.mpr
    by_contra hσ1
    have hσs : σ ∈ s := Finset.mem_erase.mpr ⟨hσ1, Finset.mem_univ _⟩
    exact (not_lt_of_ge ((hbound σ hσs).trans hn)) ((hdepth σ hσs n).mp hσ)
  have hrow (σ : Gal(L/K)) (hσ : σ ∈ s) :
      ∑ n ∈ Finset.range N, (if n < d σ then 1 else 0 : ℕ) = d σ := by
    have hfilter : (Finset.range N).filter (fun n => n < d σ) = Finset.range (d σ) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨And.right, fun hn => ⟨hn.trans_le (hbound σ hσ), hn⟩⟩
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_range]
    exact Nat.mul_one _
  have hcolumn (n : ℕ) :
      ∑ σ ∈ s, (if n < d σ then 1 else 0 : ℕ) = Nat.card (G n) - 1 := by
    let t := Finset.univ.filter (fun σ : Gal(L/K) => σ ∈ G n)
    have ht : (1 : Gal(L/K)) ∈ t :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (G n).one_mem⟩
    have hfilter : s.filter (fun σ => n < d σ) = t.erase 1 := by
      ext σ
      constructor
      · intro hσ
        obtain ⟨hσs, hσd⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hσs).1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdepth σ hσs n).mpr hσd⟩⟩
      · intro hσ
        obtain ⟨hσ1, hσt⟩ := Finset.mem_erase.mp hσ
        have hσs : σ ∈ s := Finset.mem_erase.mpr ⟨hσ1, Finset.mem_univ _⟩
        exact Finset.mem_filter.mpr ⟨hσs, (hdepth σ hσs n).mp (Finset.mem_filter.mp hσt).2⟩
    let e : (↑t : Set (Gal(L/K))) ≃ G n :=
      { toFun := fun σ => ⟨σ.1, (Finset.mem_filter.mp σ.2).2⟩
        invFun := fun σ => ⟨σ.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.2⟩⟩
        left_inv := fun σ => Subtype.ext rfl
        right_inv := fun σ => Subtype.ext rfl }
    have hcard : t.card = Nat.card (G n) := by
      have hc := Nat.card_congr e
      rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_erase_of_mem ht, hcard]
    exact Nat.mul_one _
  refine ⟨N, hbot, ?_⟩
  rw [differentIdeal_eq_maximalIdeal_pow_sum_ramificationNumbers base target huniq]
  congr 1
  change (∑ σ ∈ s, d σ) = ∑ n ∈ Finset.range N, (Nat.card (G n) - 1)
  calc
    (∑ σ ∈ s, d σ) = ∑ σ ∈ s, ∑ n ∈ Finset.range N, (if n < d σ then 1 else 0 : ℕ) :=
      Finset.sum_congr rfl (fun σ hσ => (hrow σ hσ).symm)
    _ = ∑ n ∈ Finset.range N, ∑ σ ∈ s, (if n < d σ then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ n ∈ Finset.range N, (Nat.card (G n) - 1) :=
      Finset.sum_congr rfl (fun n _ => hcolumn n)

end RamificationTheory.HilbertRamification.Higher
