/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Places.Basic

/-!
# RROpens exists finset subset ell sub sum single eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RROpensExistsFinsetSubsetEllSub

universe u v

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Module

namespace AlgebraicCurve

open _root_.AlgebraicCurve

namespace RROpensImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  have : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

private theorem degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)

section WithPack

variable {Kc : Divisor K F} {g : ℕ}

private theorem ell_canonical_eq
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (hC : ConstantsAreBase K F) : ell Kc = g := by
  have h := hRR 0
  rw [sub_zero, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
  push_cast at h
  omega

private theorem degree_add_one_sub_le_ell
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Divisor K F) : Divisor.degree E + 1 - (g : ℤ) ≤ (ell E : ℤ) := by
  have h := hRR E
  have h0 : (0 : ℤ) ≤ (ell (Kc - E) : ℤ) := Int.natCast_nonneg _
  linarith

private theorem finite_lSpace [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := degree_add_one_sub_le_ell hRR D'
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  have : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simpa only [Finsupp.single_eq_same] using (zero_le_one : (0 : ℤ) ≤ 1)
      · simp only [Finsupp.single_eq_of_ne hv, le_refl]
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

end WithPack

private theorem exists_ord_pos_of_ord_neg [IsCurveOver K F] {x : F} (hx : x ≠ 0)
    (v₀ : Place K F) (hpole : v₀.ord x < 0) : ∃ P : Place K F, 0 < P.ord x := by
  classical
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hall' : ∀ v, 0 ≤ (-D) v := fun v => by
    rw [Finsupp.neg_apply, neg_nonneg, hD v]; exact hall v
  have hv₀ : 0 < (-D) v₀ := by
    rw [Finsupp.neg_apply, neg_pos, hD v₀]; exact hpole
  have hmem : v₀ ∈ (-D).support := Finsupp.mem_support_iff.mpr hv₀.ne'
  have hdegpos : 0 < Divisor.degree (-D) := by
    rw [degree_eq_sum_support]
    calc (0 : ℤ) < (-D) v₀ * (v₀.deg : ℤ) :=
          mul_pos hv₀ (by exact_mod_cast one_le_deg v₀)
      _ ≤ ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hall' v) (Int.natCast_nonneg _)) hmem
  rw [map_neg, hdeg, neg_zero] at hdegpos
  exact lt_irrefl 0 hdegpos

private theorem infinite_place_of_pole [IsCurveOver K F] [Infinite K] {x : F}
    (v₀ : Place K F) (hpole : v₀.ord x < 0) : Infinite (Place K F) := by
  have hnotmem : x ∉ v₀.toValuationSubring := fun hmem =>
    not_lt.mpr (v₀.ord_nonneg_of_mem hmem) hpole
  have hxa_ne : ∀ a : K, x - algebraMap K F a ≠ 0 := fun a h => by
    rw [sub_eq_zero] at h
    exact hnotmem (h ▸ v₀.algebraMap_mem' a)
  have hxa_pole : ∀ a : K, x - algebraMap K F a ∉ v₀.toValuationSubring := fun a hmem =>
    hnotmem (by have := add_mem hmem (v₀.algebraMap_mem' a); rwa [sub_add_cancel] at this)
  have hxa_ord : ∀ a : K, v₀.ord (x - algebraMap K F a) < 0 := fun a => by
    by_contra hge
    exact hxa_pole a (v₀.mem_of_ord_nonneg (hxa_ne a) (not_lt.mp hge))
  have hzero : ∀ a : K, ∃ w : Place K F, 0 < w.ord (x - algebraMap K F a) := fun a =>
    exists_ord_pos_of_ord_neg (hxa_ne a) v₀ (hxa_ord a)
  choose z hz using hzero
  have hzinj : Function.Injective z := by
    intro c c' hcc'
    by_contra hne
    have h1 : 0 < (z c).ord (x - algebraMap K F c) := hz c
    have h2 : 0 < (z c).ord (x - algebraMap K F c') := by rw [hcc']; exact hz c'
    generalize z c = w at h1 h2
    have hm : ∀ {y : F}, 0 < w.ord y → ∃ hy : y ∈ w.toValuationSubring,
        (⟨y, hy⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
      intro y hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [w.ord_zero] at hy
        exact (lt_irrefl 0 hy)
      exact ⟨w.mem_of_ord_nonneg hy0 hy.le,
        (w.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos _).mpr (Or.inr hy)⟩
    obtain ⟨hx1, hm1⟩ := hm h1
    obtain ⟨hx2, hm2⟩ := hm h2
    have hdiff := Ideal.sub_mem _ hm2 hm1
    have hval : ((⟨x - algebraMap K F c', hx2⟩ : w.toValuationSubring)
        - ⟨x - algebraMap K F c, hx1⟩) = algebraMap K w.toValuationSubring (c - c') := by
      apply Subtype.ext
      simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap, map_sub]
      ring
    rw [hval] at hdiff
    have hunit : IsUnit (algebraMap K w.toValuationSubring (c - c')) :=
      (IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _
    exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit
  exact Infinite.of_injective z hzinj

private theorem infinite_place [IsAlgClosed K] [IsCurveOver K F] (P : Place K F) :
    Infinite (Place K F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hordx : P.ord ((π : F)⁻¹) < 0 := by
    rw [P.ord_inv, P.ord_coe_irreducible hπ]; decide
  exact infinite_place_of_pole P hordx

section WithPack

variable {Kc : Divisor K F} {g : ℕ}

private theorem ell_sub_single_add_one_eq [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) {G : Divisor K F} {f : F} (hfG : f ∈ LSpace G)
    (hf0 : f ≠ 0) {Q : Place K F} (hQ : Q.deg = 1) (hGQ : G Q = 0) (hfQ : Q.ord f = 0) :
    ell (G - Finsupp.single Q 1) + 1 = ell G := by
  have hfnot : f ∉ LSpace (G - Finsupp.single Q 1) := by
    intro h
    have h' := (mem_lSpace_iff_ord.mp h).resolve_left hf0 Q
    rw [Finsupp.sub_apply, Finsupp.single_eq_same, hGQ, hfQ] at h'
    omega
  have hle : LSpace (G - Finsupp.single Q 1) ≤ LSpace G := by
    refine lSpace_mono ?_
    rw [Finsupp.le_def]; intro v; rw [Finsupp.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single Q 1 v := by
      rcases eq_or_ne v Q with rfl | hv
      · rw [Finsupp.single_eq_same]; exact zero_le_one
      · rw [Finsupp.single_eq_of_ne hv]
    linarith
  have hlt : LSpace (G - Finsupp.single Q 1) < LSpace G :=
    lt_of_le_of_ne hle fun h => hfnot (h ▸ hfG)
  have : Module.Finite K (LSpace G) := finite_lSpace hRR P G
  have h1 : ell (G - Finsupp.single Q 1) < ell G := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : ell G ≤ ell (G - Finsupp.single Q 1) + Q.deg := ell_le_ell_sub_single_add_deg G Q
  rw [hQ] at h2
  omega

private theorem exists_finset_forall_ell_sub_single_add_one_eq [IsAlgClosed K] [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) {G : Divisor K F} (hG : 0 < ell G) :
    ∃ S : Finset (Place K F), ∀ Q ∉ S, ell (G - Finsupp.single Q 1) + 1 = ell G := by
  classical
  have hbot : LSpace G ≠ ⊥ := fun h => by
    have : ell G = 0 := by rw [ell, h, finrank_bot]
    omega
  obtain ⟨f, hfG, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨Δ, hΔord, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine ⟨G.support ∪ Δ.support, fun Q hQ => ?_⟩
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hQ
  obtain ⟨hGQ, hΔQ⟩ := hQ
  exact ell_sub_single_add_one_eq hRR P hfG hf0 (IsCurveOver.deg_eq_one_of_isAlgClosed Q)
    hGQ (by rw [← hΔord Q, hΔQ])

end WithPack

end RROpensImpl

namespace RROpensSubsetImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem exists_finset_subset_ell_sub_sum_single_eq_zero_impl [IsAlgClosed K] [IsCurveOver K F]
    (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (G : Divisor K F) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = ell G ∧
      ell (G - ∑ v ∈ T, Finsupp.single v 1) = 0 := by
  classical
  obtain ⟨P, -⟩ := hS.nonempty
  have step : ∀ G : Divisor K F, 0 < ell G →
      ∃ B : Finset (Place K F), ∀ Q ∉ B, ell (G - Finsupp.single Q 1) + 1 = ell G :=
    fun G hG => RROpensImpl.exists_finset_forall_ell_sub_single_add_one_eq hRR P hG
  suffices H : ∀ (n : ℕ) (S : Set (Place K F)), S.Infinite → ∀ G : Divisor K F, ell G = n →
      ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = n ∧
        ell (G - ∑ v ∈ T, Finsupp.single v 1) = 0 from H _ S hS G rfl
  intro n
  induction n with
  | zero =>
    intro S _ G hG
    refine ⟨∅, ?_, rfl, ?_⟩
    · rw [Finset.coe_empty]; exact Set.empty_subset S
    · simpa only [Finset.sum_empty, sub_zero] using hG
  | succ n ih =>
    intro S hS G hG
    obtain ⟨B, hB⟩ := step G (by omega)
    obtain ⟨v, hvS, hvB⟩ : ∃ v ∈ S, v ∉ B := by
      by_contra h
      push Not at h
      exact hS (B.finite_toSet.subset fun x hx => h x hx)
    have hv := hB v hvB
    obtain ⟨T, hTS, hTcard, hTell⟩ :=
      ih (S \ {v}) (hS.sdiff (Set.finite_singleton v)) (G - Finsupp.single v 1) (by omega)
    have hvT : v ∉ T := fun h => (hTS h).2 rfl
    refine ⟨insert v T, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hvS
      · exact (hTS hx).1
    · rw [Finset.card_insert_of_notMem hvT, hTcard]
    · rw [Finset.sum_insert hvT, ← sub_sub]
      exact hTell

end RROpensSubsetImpl

end AlgebraicCurve

end

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (G : Divisor K F) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = ell G ∧
      ell (G - ∑ v ∈ T, Finsupp.single v 1) = 0 :=
  AlgebraicCurve.RROpensSubsetImpl.exists_finset_subset_ell_sub_sum_single_eq_zero_impl Kc g hRR G
    S hS
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RROpensExistsFinsetSubsetEllSub
end ProofImplementation
