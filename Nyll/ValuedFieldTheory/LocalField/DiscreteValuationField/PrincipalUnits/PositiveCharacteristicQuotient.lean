/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
import Nyll.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
import Nyll.ValuedFieldTheory.LocalField.GroupTheory.QuotientPowers
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
import Mathlib.Data.ENat.Monoid

/-!
# Prime-power classes modulo higher principal units

In characteristic p, Frobenius detects the exact principal-unit level:
`u^p ∈ U^(pn)` if and only if `u ∈ U^n`. Thus the p-torsion in the finite
quotient `Oˣ/U^(pn)` is the actual subgroup `U^n/U^(pn)`. Counting its
successive residue-field layers computes the p-power quotient.
-/

noncomputable section
open scoped BigOperators

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField

variable {K : Type*} [Field K] (F : CompleteDVF K)

/-- Frobenius multiplies principal-unit depth exactly by p. -/
theorem pow_prime_mem_mul_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (u : F.valuationSubringˣ) :
    u ^ p ∈ higherPrincipalUnitGroup F (p * n) ↔
      u ∈ higherPrincipalUnitGroup F n := by
  have hchar : CharP F.valuationSubring p := inferInstance
  rw [mem_iff, mem_iff, Units.val_pow_eq_pow_val]
  have hfrob : (u : F.valuationSubring) ^ p - 1 =
      ((u : F.valuationSubring) - 1) ^ p := by
    rw [sub_pow_char, one_pow]
  rw [hfrob]
  change ((u : F.valuationSubring) - 1) ^ p ∈
      IsLocalRing.maximalIdeal F.valuationSubring ^ (p * n) ↔
    (u : F.valuationSubring) - 1 ∈
      IsLocalRing.maximalIdeal F.valuationSubring ^ n
  rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge,
    IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge,
    IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, Nat.cast_mul]
  exact ENat.mul_le_mul_left_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (ENat.natCast_ne_top p)

/-- The residue field counts every finite interval in the positive
principal-unit filtration. -/
theorem card_principalUnitSubquotient_eq_residue_pow
    [Finite F.residueField] (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    Nat.card (higherPrincipalUnitGroup F i ⧸
      (higherPrincipalUnitGroup F j).subgroupOf (higherPrincipalUnitGroup F i)) =
        Nat.card F.residueField ^ (j - i) := by
  obtain ⟨π, hπ⟩ := F.exists_uniformizer
  let U := toPrincipalUnitFiltration F
  have hnormal : ∀ n : ℕ, (U.principalUnitSubgroup n).Normal := fun _ => inferInstance
  have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
  calc
    Nat.card (U.principalUnitSubquotient i j) =
        Nat.card (U.principalUnitSubquotient i (i + (j - i))) := by rw [hsum]
    _ = ∏ r ∈ Finset.range (j - i), Nat.card (U.principalUnitGradedPiece (i + r)) :=
      U.card_principalUnitSubquotient_eq_prod_gradedPiece hnormal i (j - i)
    _ = ∏ _r ∈ Finset.range (j - i), Nat.card F.residueField := by
      apply Finset.prod_congr rfl
      intro r _
      exact (Nat.card_congr (principalUnitSuccQuotEquivGradedPiece F (i + r)).symm.toEquiv).trans
        (card_principalUnitSuccQuot_eq_residue_of_uniformizer F hπ (i + r) (by omega))
    _ = Nat.card F.residueField ^ (j - i) := by
      rw [Finset.prod_const, Finset.card_range]

/-- The finite unit quotient has precisely the p-power classes contributed
by the layers from n to pn. -/
theorem card_unitQuotient_primePowerQuotient
    [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : 1 ≤ n) :
    let Q := F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F (p * n)
    Nat.card (Q ⧸ (MonoidHom.range (G := Q) (N := Q) (powMonoidHom (α := Q) p))) =
      Nat.card F.residueField ^ (p * n - n) := by
  intro Q
  let f : higherPrincipalUnitGroup F n →* Q :=
    (QuotientGroup.mk' (higherPrincipalUnitGroup F (p * n))).comp
      (higherPrincipalUnitGroup F n).subtype
  have hker : f.ker = (higherPrincipalUnitGroup F (p * n)).subgroupOf
      (higherPrincipalUnitGroup F n) := by
    ext x
    exact QuotientGroup.eq_one_iff (N := higherPrincipalUnitGroup F (p * n))
      (x : F.valuationSubringˣ)
  have hrange : f.range = (powMonoidHom (α := Q) p).ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (QuotientGroup.mk' (higherPrincipalUnitGroup F (p * n))
        (y : F.valuationSubringˣ)) ^ p = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := higherPrincipalUnitGroup F (p * n))
        ((y : F.valuationSubringˣ) ^ p)).mpr
        ((pow_prime_mem_mul_iff F p n y).mpr y.property)
    · intro hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
        (higherPrincipalUnitGroup F (p * n)) x
      have hy : y ∈ higherPrincipalUnitGroup F n := by
        apply (pow_prime_mem_mul_iff F p n y).mp
        apply (QuotientGroup.eq_one_iff (N := higherPrincipalUnitGroup F (p * n))
          (y ^ p)).mp
        change QuotientGroup.mk' (higherPrincipalUnitGroup F (p * n)) (y ^ p) = 1
        rw [map_pow]
        exact hx
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ((powMonoidHom (α := Q) p).ker) =
      Nat.card (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (p * n)).subgroupOf (higherPrincipalUnitGroup F n)) := by
    rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  rw [LocalFieldTheory.card_nthPowerQuotient_eq_nthPowerKernel Q p, hcard]
  exact card_principalUnitSubquotient_eq_residue_pow F n (p * n) hn
    (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos)


/-- The actual subgroup generated by p-th powers and depth-pn principal
units has index q^(pn-n) in the valuation-ring units. -/
theorem card_units_mod_primePowers_and_principalUnits
    [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (F.valuationSubringˣ ⧸ (higherPrincipalUnitGroup F (p * n) ⊔
      (powMonoidHom (α := F.valuationSubringˣ) p).range)) =
        Nat.card F.residueField ^ (p * n - n) := by
  let e := LocalFieldTheory.quotientSupRangePowEquiv
    F.valuationSubringˣ (higherPrincipalUnitGroup F (p * n)) p
  have he := Nat.card_congr e
  exact he.trans (card_unitQuotient_primePowerQuotient F p n hn)

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
