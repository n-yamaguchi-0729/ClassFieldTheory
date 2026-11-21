/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction

/-! # The weighted Artin conductor from the Herbrand cutoff -/

@[expose] public section

noncomputable section

namespace RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration

variable {G : Type*} [Group G] [Finite G]

open Classical in
/-- The lower weighted sum, before dividing by the inertia order, is the
inertia order times the character's conductor. The cutoff in the hypothesis
uses all real Herbrand indices so it determines the last lower break exactly. -/
theorem sum_lowerWeights_eq_card_inertia_mul_of_herbrandCut
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) (c N : ℕ)
    (hN : F.lower N ≤ H)
    (hcut : ∀ s : ℝ, 0 ≤ s → (F.lower ⌈s⌉₊ ≤ H ↔ c ≤ ⌈F.herbrandFunction s⌉₊)) :
    (∑ n ∈ Finset.range N, if F.lower n ≤ H then 0 else Nat.card (F.lower n)) =
      Nat.card (F.lower 0) * c := by
  classical
  let hex : ∃ n : ℕ, F.lower n ≤ H := ⟨N, hN⟩
  let j := Nat.find hex
  have htest (n : ℕ) : F.lower n ≤ H ↔ j ≤ n := by
    constructor
    · exact Nat.find_min' hex
    · intro hn
      exact (F.antitone hn).trans (Nat.find_spec hex)
  have hjN := (htest N).mp hN
  have hsum :
      (∑ n ∈ Finset.range N, if F.lower n ≤ H then 0 else Nat.card (F.lower n)) =
        ∑ n ∈ Finset.range j, Nat.card (F.lower n) := by
    have hweight (n : ℕ) (hn : n ∈ Finset.range N) (hj' : n ∉ Finset.range j) :
        (if F.lower n ≤ H then 0 else Nat.card (F.lower n)) = 0 :=
      ite_eq_left ((htest n).mpr (Nat.le_of_not_gt (fun h => hj' (Finset.mem_range.mpr h))))
    rw [← Finset.sum_subset (Finset.range_mono hjN) hweight]
    apply Finset.sum_congr rfl
    intro n hn
    exact ite_eq_right (fun h => (Nat.not_le_of_lt (Finset.mem_range.mp hn)) ((htest n).mp h))
  have hzero : F.lower 0 ≤ H ↔ c = 0 := by
    simpa only [Nat.ceil_zero, F.herbrandFunction_zero, Nat.le_zero] using hcut 0 le_rfl
  rw [hsum]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · have hc := hzero.mp ((htest 0).mpr hj.le)
    simp only [hj, hc, Finset.range_zero, Finset.sum_empty, Nat.mul_zero]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hc : c ≠ 0 := fun hc => hj.ne' (Nat.le_zero.mp ((htest 0).mp (hzero.mpr hc)))
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hc
    have htestReal (s : ℝ) (hs : 0 ≤ s) :
        (m : ℝ) < s ↔ (k : ℝ) < F.herbrandFunction s := by
      have hh := hcut s hs
      rw [htest, hm, hk, Nat.succ_le_iff, Nat.succ_le_iff, Nat.lt_ceil, Nat.lt_ceil] at hh
      exact hh
    have hphi : F.herbrandFunction (m : ℝ) = k := by
      apply le_antisymm
      · exact le_of_not_gt (fun h => (lt_irrefl (m : ℝ)) ((htestReal m (Nat.cast_nonneg m)).mpr h))
      · apply le_of_not_gt
        intro hm_lt
        let s := F.inverseHerbrandFunction (k : ℝ)
        have hs0 : F.herbrandFunction s = k := F.herbrandFunction_inverseHerbrandFunction _
        have hm_lt_s : (m : ℝ) < s := F.herbrandFunction_strictMono.lt_iff_lt.mp (by rwa [hs0])
        have hs : 0 ≤ s := (Nat.cast_nonneg m).trans hm_lt_s.le
        have h := (htestReal s hs).mp hm_lt_s
        rw [hs0] at h
        exact (lt_irrefl _ h)
    have hw : (∑ n ∈ Finset.range m, Nat.card (F.lower (n + 1))) =
        Nat.card (F.lower 0) * k := by
      have hcard : (Nat.card (F.lower 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Finite.card_pos.ne'
      have hmul : (∑ n ∈ Finset.range m, (Nat.card (F.lower (n + 1)) : ℝ)) =
          (Nat.card (F.lower 0) : ℝ) * (k : ℝ) := by
        rw [← hphi, F.herbrandFunction_nat, herbrandValueNat, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [herbrandSlope, ← mul_div_assoc, mul_div_cancel_left₀ _ hcard]
      exact_mod_cast hmul
    rw [hm, hk, Finset.sum_range_succ', hw, Nat.mul_succ]

end RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration

namespace RamificationTheory.HilbertRamification.Higher

open ValuationTheory.DiscreteValuationField
open RamificationTheory.DiscreteValuationField.DVF (HasUniqueValuationExtension)

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : DVF.{u, v} K} {target : DVF.{w, x} L}
  [base.valuation.HasExtension target.valuation]

/-- The nonnegative real lower filtration is obtained by taking the ceiling
of the lower index. -/
theorem lowerRamificationGroup_eq_ceil_of_nonneg
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target) (s : ℝ) (hs : 0 ≤ s) :
    lowerRamificationGroup (base := base) (target := target) huniq s =
      lowerRamificationGroup (base := base) (target := target) huniq (⌈s⌉₊ : ℕ) := by
  have hexp : realRamificationExponent s = ⌈s⌉₊ + 1 := by
    rw [realRamificationExponent, ← Int.natCast_ceil_eq_ceil (by linarith : 0 ≤ s + 1),
      Int.toNat_natCast, Nat.ceil_add_one hs]
  ext σ
  simp only [mem_lowerRamificationGroup_iff, realRamificationIdeal, hexp,
    realRamificationExponent_nat]

end RamificationTheory.HilbertRamification.Higher
