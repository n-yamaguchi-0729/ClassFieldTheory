/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Evaluation.Value
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place has Value iff mem and eq or ord sub pos
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_hasValue_iff_mem_and_eq_or_ord_sub_pos

open _root_.AlgebraicCurve
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_e15 {g : F} (hg : g ∈
  v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := by
      apply Subtype.ext
      change g - algebraMap K F c =
        g - ((algebraMap K v.toValuationSubring c : v.toValuationSubring) : F)
      rw [v.coe_algebraMap]
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => Ideal.zero_mem _⟩
  · rw [v.mem_maximalIdeal_iff_ord_pos h0 hsub]
    constructor
    · exact Or.inr
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact hpos

open _root_.AlgebraicCurve.Place

theorem div_mem_of_ord_le_e15 {r t : F} (ht : t ≠ 0) (h : v.ord t ≤ v.ord r) :
    r / t ∈ v.toValuationSubring := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [zero_div]
    exact zero_mem _
  · apply v.mem_of_ord_nonneg (div_ne_zero hr ht)
    rw [div_eq_mul_inv, v.ord_mul hr (inv_ne_zero ht), v.ord_inv]
    omega

theorem tExpansion_coeff_unique_e15 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
    (hc : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c i) * t ^ i) / t ^ m ∈
      v.toValuationSubring)
    (hc' : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c' i) * t ^ i) / t ^ m ∈
      v.toValuationSubring) :
    c = c' := by
  classical
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at ht
    exact (lt_irrefl 0) ht
  by_contra hne
  have hex : ∃ m, c m ≠ c' m := by
    by_contra hall
    exact hne (funext fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm, hmin⟩ : ∃ m, c m ≠ c' m ∧ ∀ i < m, c i = c' i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  set e : K := c m - c' m with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hm
  have hdiff : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) / t ^ (m + 1) -
      (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) / t ^ (m + 1) =
      algebraMap K F e / t := by
    rw [← sub_div]
    have hnum : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) -
        (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) =
        algebraMap K F e * t ^ m := by
      have hs : ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i -
          ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i =
          algebraMap K F e * t ^ m := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
          ← sub_mul, ← map_sub]
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hmin i hi, sub_self]
      rw [← hs]; ring
    rw [hnum, pow_succ, mul_comm (t ^ m) t, mul_div_mul_right _ _ (pow_ne_zero m ht0)]
  have hmem : algebraMap K F e / t ∈ v.toValuationSubring := by
    rw [← hdiff]; exact sub_mem (hc' (m + 1)) (hc (m + 1))
  have hord : v.ord (algebraMap K F e / t) < 0 := by
    have hae : algebraMap K F e ≠ 0 := (_root_.map_ne_zero _).mpr he0
    rw [div_eq_mul_inv, v.ord_mul hae (inv_ne_zero ht0), v.ord_inv, v.ord_algebraMap]
    omega
  exact absurd (v.ord_nonneg_of_mem hmem) (not_le.mpr hord)

end Place
end AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_e15 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_e15 hg c).mpr h
end AlgebraicCurves.Places.Proofs.Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
end ProofImplementation
