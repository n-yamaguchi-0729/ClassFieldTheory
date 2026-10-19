/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Pic0_mk_eq_zero_iff
- Pic0_zsmul_mk
- Pic0_subsingleton_of_forall_isPrincipal
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Picard Zero
-/

section

/-!
# Pic0 mk eq zero iff
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_mk_eq_zero_iff

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
  (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F)
  := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  exact Divisor.mem_principal
end JacobianVarieties.Pic0.Proofs.Pic0_mk_eq_zero_iff
end ProofImplementation

end

section

/-!
# Pic0 zsmul mk
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_zsmul_mk

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.zsmul_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (m : ℤ)
  (D : Divisor.degZero (K := K) (F := F)) : m • Pic0.mk D = Pic0.mk (m • D) :=
  (map_zsmul (QuotientAddGroup.mk' _) m D).symm
end JacobianVarieties.Pic0.Proofs.Pic0_zsmul_mk
end ProofImplementation

end

section

/-!
# Pic0 subsingleton of forall is Principal
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_subsingleton_of_forall_isPrincipal

open IsDedekindDomain WithZero IsLocalRing

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal (K F : Type*) [Field K]
  [Field F] [Algebra K F]
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) :=
  (QuotientAddGroup.subsingleton_iff.trans AddSubgroup.addSubgroupOf_eq_top).mpr
    fun D hD => Divisor.mem_principal.mpr (h D hD)
end JacobianVarieties.Pic0.Proofs.Pic0_subsingleton_of_forall_isPrincipal
end ProofImplementation

end

section

/-!
# Generation of the degree-zero Picard group by point differences
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_mem_closure_mk_single_sub_single
open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (h1 : ∀ v : Place K F, v.deg = 1)
    (V₀ : Place K F) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hgen : ∀ v : Place K F,
      Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1 ∈
        Divisor.degZero (K := K) (F := F) := fun v => by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      h1, h1, sub_self]
  set g : Place K F → ↥(Divisor.degZero (K := K) (F := F)) := fun v => ⟨_, hgen v⟩ with hg
  have hdeg : ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v = 0 := by
    have h0 : Divisor.degree (D : Divisor K F) = 0 := Divisor.mem_degZero.mp D.2
    have : Divisor.degree (D : Divisor K F) =
        ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v * ((v.deg : ℕ) : ℤ) := by
      change Finsupp.liftAddHom _ (D : Divisor K F) = _
      rw [Finsupp.liftAddHom_apply, Finsupp.sum]
      rfl
    rw [this] at h0
    simpa only [h1, Nat.cast_one, mul_one] using h0
  have hD : D = ∑ v ∈ (D : Divisor K F).support, ((D : Divisor K F) v) • g v := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    simp only [AddSubgroupClass.coe_zsmul, hg, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hdeg, zero_smul, sub_zero]
    simp only [Finsupp.smul_single_one]
    exact ((D : Divisor K F).sum_single).symm
  have hφ : ∀ E, Pic0.mk (K := K) (F := F) E =
      QuotientAddGroup.mk' ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) E :=
    fun E => rfl
  have hmem : ∀ v : Place K F, Pic0.mk (g v) ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} :=
    fun v => AddSubgroup.subset_closure ⟨v, hgen v, rfl⟩
  rw [hD, hφ, map_sum]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (hmem v) _
end JacobianVarieties.Pic0.Proofs.Pic0_mem_closure_mk_single_sub_single
end ProofImplementation

end
