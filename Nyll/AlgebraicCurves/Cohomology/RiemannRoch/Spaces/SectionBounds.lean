/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_eq_zero_of_degree_neg.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_le_ell_sub_single_add_deg.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_le_degree_add_ellZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic
import Mathlib.Tactic.Linarith
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-! Elementary section bounds: negative degree, removal of a place, and effective divisors. -/

section

/-! A divisor of negative degree has no nonzero section. -/

open AlgebraicCurve Module

theorem _root_.AlgebraicCurve.lSpace_eq_bot_of_degree_neg {K F : Type*} [Field K] [Field F]
  [Algebra K F] {D : Divisor K F} [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)

end

section

/-! The section dimension of a divisor of negative degree is zero. -/

open AlgebraicCurve Module

theorem _root_.AlgebraicCurve.ell_eq_zero_of_degree_neg {K F : Type*} [Field K] [Field F] [Algebra
    K F] {D : Divisor K F} [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]

end

section

/-! Removing a point decreases the section dimension by at most its degree. -/

open AlgebraicCurve Module

theorem _root_.AlgebraicCurve.ell_le_ell_sub_single_add_deg {K F : Type*} [Field K] [Field F]
  [Algebra K F] [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by
  classical
  have : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by
    simpa only [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0
  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := by
    intro g hg
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]
  have hmem : ∀ g : F, g ∈ LSpace D → t ^ (D P) * g ∈ P.toValuationSubring := by
    intro g hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa only [mul_zero] using P.toValuationSubring.zero_mem
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have := (mem_lSpace_iff_ord.mp hg).resolve_left hg0 P
      linarith
  let ψ : LSpace D →ₗ[K] P.toValuationSubring :=
    { toFun := fun f => ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
      map_add' := by intro f g; apply Subtype.ext; push_cast; ring
      map_smul' := by
        intro c f; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap]
        ring }
  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    change (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : LSpace D →ₗ[K] P.ResidueField := res ∘ₗ ψ
  have hphi : ∀ f : LSpace D, φ f = 0 ↔
      (⟨t ^ (D P) * (f : F), hmem _ f.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    intro f
    rw [show φ f = IsLocalRing.residue P.toValuationSubring ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
          from hres (ψ f),
      IsLocalRing.residue_eq_zero_iff]
  have hED : E ≤ D := by
    rw [Finsupp.le_def]; intro v; rw [hE, Finsupp.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simpa only [Finsupp.single_eq_same] using (zero_le_one : (0 : ℤ) ≤ 1)
      · simp only [Finsupp.single_eq_of_ne hv, le_refl]
    linarith
  have hsub : LSpace E ≤ LSpace D := lSpace_mono hED
  have hker : LinearMap.ker φ = (LSpace E).comap (LSpace D).subtype := by
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi f, P.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos]
    rcases eq_or_ne (f : F) 0 with hf0 | hf0
    · simp only [hf0, mul_zero, true_or, true_iff]
      exact (LSpace E).zero_mem
    · rw [mem_lSpace_iff_ord]
      have hfD := (mem_lSpace_iff_ord.mp f.2).resolve_left hf0
      constructor
      · rintro (h | h)
        · exact absurd h (mul_ne_zero htn0 hf0)
        · refine Or.inr (fun v => ?_)
          rcases eq_or_ne v P with rfl | hv
          · rw [hEP]; rw [hordmul hf0] at h; omega
          · rw [hEv v hv]; exact hfD v
      · rintro (h | h)
        · exact absurd h hf0
        · refine Or.inr ?_
          have hP := h P
          rw [hEP] at hP
          rw [hordmul hf0]; omega
  have hkerfin : finrank K (LinearMap.ker φ) = ell E := by
    rw [hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hsub)]
  have hquot : finrank K (LSpace D ⧸ LinearMap.ker φ) ≤ P.deg := by
    rw [LinearEquiv.finrank_eq φ.quotKerEquivRange]
    exact Submodule.finrank_le (LinearMap.range φ)
  by_cases hfin : FiniteDimensional K (LSpace D)
  · have := hfin
    have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker φ)
    rw [hkerfin] at hrn
    have hb : ell D = finrank K (LSpace D) := rfl
    omega
  · have h0 : ell D = 0 := by rw [ell]; exact finrank_of_infinite_dimensional hfin
    omega

end

section

/-! The section dimension of an effective divisor is bounded by its degree and the constants. -/

open AlgebraicCurve Module

theorem _root_.AlgebraicCurve.ell_le_degree_add_ellZero {K F : Type*} [Field K] [Field F] [Algebra
  K F] [IsCurveOver K F] {D : Divisor K F}
    (hD : 0 ≤ D) [FiniteDimensional K ↥(LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by
  classical
  suffices H : ∀ m : ℕ, ∀ D : Divisor K F, (∀ v, 0 ≤ D v) →
      (Divisor.degree D).toNat = m →
      (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) by
    exact H (Divisor.degree D).toNat D hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D hD hm
    by_cases hD0 : D = 0
    · subst hD0; rw [map_zero, zero_add]
    · obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ D P := by
        have hne : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hD P; omega
      set E : Divisor K F := D - Finsupp.single P 1 with hE
      have hEeff : ∀ v, 0 ≤ E v := by
        intro v; rw [hE, Finsupp.sub_apply]
        rcases eq_or_ne v P with rfl | hv
        · rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have hdegE : Divisor.degree E = Divisor.degree D - P.deg := by
        rw [hE, map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by
        have : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
        exact_mod_cast (Module.finrank_pos : 1 ≤ Module.finrank K P.ResidueField)
      have hDnn : 0 ≤ Divisor.degree D := Divisor.degree_nonneg_of_nonneg hD
      have hEnn : 0 ≤ Divisor.degree E := Divisor.degree_nonneg_of_nonneg hEeff
      have hmlt : (Divisor.degree E).toNat < m := by rw [← hm]; omega
      have hIH := IH _ hmlt E hEeff rfl
      have hstep := ell_le_ell_sub_single_add_deg D P
      rw [← hE] at hstep
      have hstep' : (ell D : ℤ) ≤ (ell E : ℤ) + P.deg := by exact_mod_cast hstep
      rw [hdegE] at hIH
      linarith

end
