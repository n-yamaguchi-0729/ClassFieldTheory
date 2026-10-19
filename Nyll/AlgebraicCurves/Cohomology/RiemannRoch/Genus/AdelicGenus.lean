/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finiteDimensional_lSpace.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_omegaSpace_finite_of_genusReached.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_riemannIndexFormula_of_genusReached.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_adeleSpace_eq_of_genusReached.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

/-! Bounded adelic quotients, attained genus, and their section and differential dimensions. -/

section

/-!
# The index of specialty when the Riemann genus is reached

Bounded adelic quotients give finite dimensionality and the Riemann–Roch dimension formula for
the index of specialty when a divisor reaches the genus bound.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.IndexOfSpecialty_eq_of_genusReached

noncomputable section

open _root_.Module _root_.IsLocalRing _root_.IsDedekindDomain _root_.WithZero

namespace AlgebraicCurve

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  have : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

theorem ell_le_degree_add_ellZero [IsCurveOver K F] {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) :
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
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
      have hDnn : 0 ≤ Divisor.degree D := Divisor.degree_nonneg_of_nonneg hD
      have hEnn : 0 ≤ Divisor.degree E := Divisor.degree_nonneg_of_nonneg hEeff
      have hmlt : (Divisor.degree E).toNat < m := by rw [← hm]; omega
      have hIH := IH _ hmlt E hEeff rfl
      have hstep := ell_le_ell_sub_single_add_deg D P
      rw [← hE] at hstep
      have hstep' : (ell D : ℤ) ≤ (ell E : ℤ) + P.deg := by exact_mod_cast hstep
      rw [hdegE] at hIH
      linarith

theorem ell_le_degree_add_one_of_effective [IsCurveOver K F]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  have h := ell_le_degree_add_ellZero hD
  rw [ell_zero_eq_one_of_constantsAreBase hC] at h
  exact_mod_cast h

/-- Multiplication by the inverse of a nonzero function identifies the Riemann–Roch space
for `D` with the space for `D + Dg`, where `Dg` records the orders of that function. -/
def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    change (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    change (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]

theorem ell_le_degree_add_one [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {D : Divisor K F} (hD : 0 ≤ Divisor.degree D) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  rcases eq_or_ne (ell D) 0 with h0 | h0
  · rw [h0]; push_cast; linarith
  · have hbot : LSpace D ≠ ⊥ := fun h => h0 (by rw [ell, h, finrank_bot])
    obtain ⟨g, hgL, hg0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨Dg, hDgord, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
    have heff : ∀ v, 0 ≤ (D + Dg) v := by
      intro v; rw [Finsupp.add_apply, hDgord]
      have := (mem_lSpace_iff_ord.mp hgL).resolve_left hg0 v
      linarith
    have hdeg : Divisor.degree (D + Dg) = Divisor.degree D := by
      rw [map_add, hDgdeg, add_zero]
    have hell : ell D = ell (D + Dg) :=
      LinearEquiv.finrank_eq (lSpaceShiftEquiv D hg0 hDgord)
    have hfin := ell_le_degree_add_one_of_effective hC heff
    rw [hdeg] at hfin
    rw [hell]; exact hfin

end AlgebraicCurve

end

noncomputable section

open _root_.Module
open _root_.IsLocalRing
open _root_.IsDedekindDomain
open _root_.WithZero

namespace Submodule
open _root_.Submodule
open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- For nested submodules, identify the image of `B` in the quotient of `C` by `A`
with the quotient of `B` by the induced submodule from `A`. -/
def nestedComapMapMkQEquiv {A B C : Submodule K X} (_hAB : A ≤ B) (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT
  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))
  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

theorem finrank_quotient_chain {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCB : Module.Finite K (C ⧸ B.comap C.subtype)]
    [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (C ⧸ A.comap C.subtype) ∧
      finrank K (C ⧸ A.comap C.subtype)
        = finrank K (C ⧸ B.comap C.subtype) + finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB
  have e3 := Submodule.quotientQuotientEquivQuotient S T hST
  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  have : Module.Finite K (T.map S.mkQ : Submodule K _) := Module.Finite.equiv eK.symm
  have : Module.Finite K ((C ⧸ S) ⧸ T.map S.mkQ) := Module.Finite.equiv e3.symm
  have hfin : Module.Finite K (C ⧸ S) := Module.Finite.of_submodule_quotient (T.map S.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

theorem finrank_quotient_chain' {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCA : Module.Finite K (C ⧸ A.comap C.subtype)] :
    Module.Finite K (C ⧸ B.comap C.subtype) ∧
      finrank K (C ⧸ B.comap C.subtype)
        = finrank K (C ⧸ A.comap C.subtype) - finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB
  have e3 := Submodule.quotientQuotientEquivQuotient S T hST
  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  have : Module.Finite K (C ⧸ T) := Module.Finite.equiv e3
  refine ⟨this, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

end Submodule

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Identify the quotient of bounded adeles obtained by lowering the divisor coefficient
at one place by one with that place's residue field. -/
def adeleBddQuotSingleEquivResidueField (D : Divisor K F) (P : Place K F) :
    (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
      ≃ₗ[K] P.ResidueField := by
  classical
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]
  let π : P.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose_spec
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0
  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := fun {g} hg => by
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]
  have hmem : ∀ α : Place K F → F, α ∈ adeleBdd D → t ^ (D P) * α P ∈ P.toValuationSubring := by
    intro α hα
    rcases eq_or_ne (α P) 0 with hg0 | hg0
    · rw [hg0, mul_zero]; exact zero_mem _
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have h := hα P
      rw [P.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
      linarith
  let ψ : adeleBdd D →ₗ[K] P.toValuationSubring :=
    { toFun := fun α => ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩
      map_add' := by
        intro α β; apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply]
        push_cast; ring
      map_smul' := by
        intro c α; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap, Pi.smul_apply]
        ring }
  have hψ_apply : ∀ α : adeleBdd D,
      (ψ α : F) = t ^ (D P) * (α : Place K F → F) P := fun α => rfl
  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    change (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : adeleBdd D →ₗ[K] P.ResidueField := res ∘ₗ ψ
  have hphi : ∀ α : adeleBdd D, φ α = 0 ↔
      (⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := fun α => by
    rw [show φ α = IsLocalRing.residue P.toValuationSubring
            ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ from hres (ψ α),
      IsLocalRing.residue_eq_zero_iff]
  have hker : LinearMap.ker φ = (adeleBdd E).comap (adeleBdd D).subtype := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi α, P.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos, mem_adeleBdd]
    have hαD := α.2
    constructor
    · rintro (h | h) v
      · have hα0 : (α : Place K F → F) P = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' htn0
          · exact h'
        by_cases hv : v = P
        · subst v; rw [hα0, Valuation.map_zero]; exact zero_le
        · rw [hEv v hv]; exact hαD v
      · by_cases hv : v = P
        · subst v
          rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
          · rw [hα0, Valuation.map_zero]; exact zero_le
          · rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP]
            rw [hordmul hα0] at h; omega
        · rw [hEv v hv]; exact hαD v
    · intro h
      rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
      · left; rw [hα0, mul_zero]
      · right
        have hP := h P
        rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP] at hP
        rw [hordmul hα0]; omega
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨cl, hcl⟩ := IsLocalRing.residue_surjective (R := P.toValuationSubring) c
    set f : F := (cl : F) * t ^ (-(D P)) with hf
    have hαD : Pi.single P f ∈ adeleBdd D := by
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Pi.single_eq_same]
        rcases eq_or_ne (cl : F) 0 with hc0 | hc0
        · rw [hf, hc0, zero_mul, Valuation.map_zero]; exact zero_le
        · have hf0 : f ≠ 0 := by rw [hf]; exact mul_ne_zero hc0 (zpow_ne_zero _ ht0)
          rw [P.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_le_exp]
          rw [hf, P.ord_mul hc0 (zpow_ne_zero _ ht0), P.ord_zpow, ht1, mul_one]
          have hclnn := P.ord_nonneg_of_mem cl.2
          linarith
      · rw [Pi.single_eq_of_ne hv, Valuation.map_zero]; exact zero_le
    refine ⟨⟨Pi.single P f, hαD⟩, ?_⟩
    change res (ψ ⟨Pi.single P f, hαD⟩) = c
    rw [hres]
    rw [show (ψ ⟨Pi.single P f, hαD⟩ : P.toValuationSubring) = cl from ?_, hcl]
    apply Subtype.ext
    rw [hψ_apply]
    change t ^ (D P) * (Pi.single P f : Place K F → F) P = (cl : F)
    rw [show (Pi.single P f : Place K F → F) P = f from Pi.single_eq_same _ _, hf,
      mul_comm (cl : F), ← mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, one_mul]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hsurj)

theorem finrank_adeleBdd_quotient_single [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    Module.Finite K
        (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype) ∧
      finrank K
          (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
        = P.deg := by
  have := IsCurveOver.finite_residueField (K := K) P
  exact ⟨Module.Finite.equiv (adeleBddQuotSingleEquivResidueField D P).symm,
    (adeleBddQuotSingleEquivResidueField D P).finrank_eq⟩

theorem finrank_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
        = Divisor.degree D₂ - Divisor.degree D₁ := by
  classical
  suffices H : ∀ m : ℕ, ∀ D₁ D₂ : Divisor K F, D₁ ≤ D₂ →
      (Divisor.degree (D₂ - D₁)).toNat = m →
      Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
        (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
          = Divisor.degree D₂ - Divisor.degree D₁ from
    H _ D₁ D₂ hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D₁ D₂ hD hm
    have hEeff : ∀ v, 0 ≤ (D₂ - D₁) v := fun v => by
      rw [Finsupp.sub_apply]; have := hD v; omega
    by_cases hD0 : D₂ - D₁ = 0
    · have hD12 : D₁ = D₂ := (sub_eq_zero.mp hD0).symm
      subst hD12
      rw [Submodule.comap_subtype_self]
      have : Subsingleton (adeleBdd D₁ ⧸ (⊤ : Submodule K (adeleBdd D₁))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact ⟨Module.Finite.of_finite, by
        rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_self]⟩
    · obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ (D₂ - D₁) P := by
        have hne : (D₂ - D₁) P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hEeff P; omega
      set D₂' : Divisor K F := D₂ - Finsupp.single P 1 with hD₂'
      have h12' : D₁ ≤ D₂' := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]
          have := hPpos; rw [Finsupp.sub_apply] at this; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have h2'2 : D₂' ≤ D₂ := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]
      have hdegD₂' : Divisor.degree D₂' = Divisor.degree D₂ - P.deg := by
        rw [hD₂', map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
      have hEnn : 0 ≤ Divisor.degree (D₂ - D₁) := Divisor.degree_nonneg_of_nonneg hEeff
      have hE'nn : 0 ≤ Divisor.degree (D₂' - D₁) := Divisor.degree_nonneg_of_nonneg
        (fun v => by rw [Finsupp.sub_apply]; have := h12' v; omega)
      have hdegdiff : Divisor.degree (D₂' - D₁) = Divisor.degree (D₂ - D₁) - P.deg := by
        simp only [hD₂', map_sub, Divisor.degree_single, one_mul]; ring
      have hmlt : (Divisor.degree (D₂' - D₁)).toNat < m := by rw [← hm]; omega
      obtain ⟨hfin', hrank'⟩ := IH _ hmlt D₁ D₂' h12' rfl
      obtain ⟨hfinS, hrankS⟩ := finrank_adeleBdd_quotient_single (K := K) D₂ P
      rw [← hD₂'] at hfinS hrankS
      have := hfin'; have := hfinS
      obtain ⟨hfin, hrank⟩ := Submodule.finrank_quotient_chain
        (A := adeleBdd D₁) (B := adeleBdd D₂') (C := adeleBdd D₂)
        (adeleBdd_mono h12') (adeleBdd_mono h2'2)
      refine ⟨hfin, ?_⟩
      rw [hrank, hrankS]
      push_cast
      linarith [hrank', hdegD₂']

theorem module_finite_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  (finrank_adeleBdd_quotient hD).1

theorem finrank_adeleBdd_quotient_eq [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
      = Divisor.degree D₂ - Divisor.degree D₁ :=
  (finrank_adeleBdd_quotient hD).2

/-- The diagonal embedding induces a map from a quotient of Riemann–Roch spaces
to the corresponding quotient of bounded adelic spaces. -/
def lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (_hD : D₁ ≤ D₂) :
    (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      →ₗ[K] (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  Submodule.mapQ _ _
    ((diagonalHom K F).restrict
      (p := (LSpace D₂ : Submodule K F)) (q := (adeleBdd D₂ : Submodule K _))
      (fun f hf => diagonal_mem_adeleBdd_iff.mpr hf))
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf ⊢
      exact diagonal_mem_adeleBdd_iff.mpr hf)

theorem lSpaceQuotientToAdeleBddQuotient_injective {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Function.Injective (lSpaceQuotientToAdeleBddQuotient hD) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk ((diagonalHom K F).restrict
            (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f) from rfl,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hx
  exact diagonal_mem_adeleBdd_iff.mp hx


theorem ell_sub_ell_le_degree_sub_degree [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by
  have := module_finite_adeleBdd_quotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    rw [hℓ₁]; exact (Submodule.finrank_quotient_add_finrank _).symm
  have hemb : finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      ≤ finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
    LinearMap.finrank_le_finrank_of_injective (lSpaceQuotientToAdeleBddQuotient_injective hD)
  have hloc := finrank_adeleBdd_quotient_eq hD
  have : (ell D₂ : ℤ) - (ell D₁ : ℤ)
      = (finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) : ℤ) := by
    rw [hL]; push_cast; ring
  rw [this, ← hloc]
  exact_mod_cast hemb

theorem adeleBdd_inf_sup_globalSub {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F)
      = adeleBdd D₁ ⊔ adeleBdd D₂ ⊓ globalSub K F := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleBdd_mono hD), inf_comm]

theorem map_diagonal_lSpace_inf_adeleBdd {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (LSpace D₂).map (diagonalHom K F) ⊓ adeleBdd D₁ = (LSpace D₁).map (diagonalHom K F) := by
  rw [map_diagonal_lSpace, map_diagonal_lSpace, inf_right_comm,
    inf_eq_right.mpr (adeleBdd_mono hD)]

theorem gate_finrank_adeleBdd_quotient_single_point [IsCurveOver K F] (P : Place K F) :
    (finrank K (adeleBdd (Finsupp.single P 1 : Divisor K F)
        ⧸ (adeleBdd (0 : Divisor K F)).comap (adeleBdd (Finsupp.single P 1)).subtype) : ℤ)
      = (P.deg : ℤ) := by
  classical
  have h01 : (0 : Divisor K F) ≤ Finsupp.single P 1 := by
    intro v; rw [Finsupp.zero_apply, Finsupp.single_apply]; split_ifs <;> omega
  have h := finrank_adeleBdd_quotient_eq (K := K) h01
  rw [h, map_zero, sub_zero, Divisor.degree_single, one_mul]

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace Submodule
open _root_.Submodule
open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem comap_subtype_sup_of_le_of_le {S T C : Submodule K X} (hS : S ≤ C) (hT : T ≤ C) :
    S.comap C.subtype ⊔ T.comap C.subtype = (S ⊔ T).comap C.subtype := by
  apply Submodule.map_injective_of_injective (f := C.subtype) C.subtype_injective
  rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, inf_eq_right.mpr hS, inf_eq_right.mpr hT,
    inf_eq_right.mpr (sup_le hS hT)]

theorem finrank_quotient_chain_top {M : Type*} [AddCommGroup M] [Module K M]
    {A B : Submodule K M} (hAB : A ≤ B)
    [hMB : Module.Finite K (M ⧸ B)] [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (M ⧸ A) ∧
      finrank K (M ⧸ A) = finrank K (M ⧸ B) + finrank K (B ⧸ A.comap B.subtype) := by
  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  let ψ : (B : Type _) →ₗ[K] (M ⧸ A) := A.mkQ ∘ₗ B.subtype
  have hker : LinearMap.ker ψ = A.comap B.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = B.map A.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let eK : (B ⧸ A.comap B.subtype) ≃ₗ[K] (B.map A.mkQ : Submodule K (M ⧸ A)) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))
  have : Module.Finite K (B.map A.mkQ : Submodule K (M ⧸ A)) := Module.Finite.equiv eK
  have : Module.Finite K ((M ⧸ A) ⧸ B.map A.mkQ) := Module.Finite.equiv e3.symm
  have hfin : Module.Finite K (M ⧸ A) := Module.Finite.of_submodule_quotient (B.map A.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (B.map A.mkQ)
  rw [LinearEquiv.finrank_eq e3, ← LinearEquiv.finrank_eq eK] at h
  omega

end Submodule

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem globalSub_le_adeleSpace [HasPrincipalDivisors K F] :
    globalSub K F ≤ adeleSpace K F := by
  rintro _ ⟨f, rfl⟩
  exact diagonal_mem_adeleSpace f

theorem adeleBdd_sup_globalSub_le_adeleSpace [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
  sup_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

theorem adeleBddPrincipal_eq_comap [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBddPrincipal K F D = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype :=
  Submodule.comap_subtype_sup_of_le_of_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

theorem adeleBddPrincipal_mono {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBddPrincipal K F D₁ ≤ adeleBddPrincipal K F D₂ :=
  sup_le_sup_right (Submodule.comap_mono (adeleBdd_mono hD)) _

section FiniteLSpace

variable [IsCurveOver K F] [Nonempty (Place K F)]

omit [Nonempty (Place K F)] in
theorem finiteDimensional_lSpace [hL0 : FiniteDimensional K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K (LSpace D) := by
  have h0D : (0 : Divisor K F) ≤ D ⊔ 0 := le_sup_right
  have hDD : D ≤ D ⊔ 0 := le_sup_left
  suffices h : FiniteDimensional K (LSpace (D ⊔ 0)) by
    exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hDD))
      (Submodule.inclusion_injective _)
  have := module_finite_adeleBdd_quotient (K := K) h0D
  have hfinQ : FiniteDimensional K
      (LSpace (D ⊔ 0) ⧸ (LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype) :=
    Module.Finite.of_injective _ (lSpaceQuotientToAdeleBddQuotient_injective h0D)
  have : FiniteDimensional K
      ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype : Submodule K _) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (lSpace_mono h0D)).symm
  exact Module.Finite.of_submodule_quotient
    ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype)

end FiniteLSpace


theorem range_lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD)
      = ((adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype).map
          ((adeleBdd D₁).comap (adeleBdd D₂).subtype).mkQ := by
  classical
  ext z
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mkQ_apply]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hxeq : Submodule.Quotient.mk
        ((diagonalHom K F).restrict (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f)
        = (Submodule.Quotient.mk α :
            adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) := hx
    refine ⟨α, ?_, rfl⟩
    have hdiag2 : (diagonalHom K F (f : F)) ∈ adeleBdd D₂ := diagonal_mem_adeleBdd_iff.mpr f.2
    have hsub : (α : Place K F → F) - diagonalHom K F (f : F) ∈ adeleBdd D₁ := by
      have hq := (Submodule.Quotient.eq _).mp hxeq.symm
      exact Submodule.mem_comap.mp hq
    refine Submodule.mem_sup.mpr ⟨(α : Place K F → F) - diagonalHom K F (f : F), hsub,
      diagonalHom K F (f : F), diagonal_mem_globalSub _, ?_⟩
    abel
  · rintro ⟨β, hβ, hβeq⟩
    have hβ' : (β : Place K F → F) ∈ adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F) :=
      Submodule.mem_inf.mpr ⟨β.2, hβ⟩
    rw [adeleBdd_inf_sup_globalSub hD, ← map_diagonal_lSpace] at hβ'
    obtain ⟨γ, hγ, δ, ⟨f, hf, hfδ⟩, hsum⟩ := Submodule.mem_sup.mp hβ'
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, ?_⟩
    rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk ⟨f, hf⟩)
          = Submodule.Quotient.mk ((diagonalHom K F).restrict
              (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) ⟨f, hf⟩) from rfl,
      ← hβeq, Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    change diagonalHom K F f - (β : Place K F → F) ∈ adeleBdd D₁
    have hβsub : diagonalHom K F f - (β : Place K F → F) = -γ := by
      rw [← hsum, hfδ]; ring
    rw [hβsub]; exact (adeleBdd D₁).neg_mem hγ


theorem finrank_adeleBddSup_quotient [IsCurveOver K F] [Nonempty (Place K F)]
    {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) [hL : FiniteDimensional K (LSpace D₂)] :
    Module.Finite K (↥(adeleBdd D₂ ⊔ globalSub K F)
        ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) ∧
      (finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
          ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) : ℤ)
        = (Divisor.degree D₂ - ell D₂) - (Divisor.degree D₁ - ell D₁) := by
  classical
  let A : Submodule K (adeleBdd D₂) := (adeleBdd D₁).comap (adeleBdd D₂).subtype
  let B : Submodule K (adeleBdd D₂) :=
    (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype
  have hAB : A ≤ B := Submodule.comap_mono le_sup_left
  have hfinA : Module.Finite K (adeleBdd D₂ ⧸ A) := module_finite_adeleBdd_quotient hD
  have hdimA : (finrank K (adeleBdd D₂ ⧸ A) : ℤ) = Divisor.degree D₂ - Divisor.degree D₁ :=
    finrank_adeleBdd_quotient_eq hD
  have hran : LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD) = B.map A.mkQ :=
    range_lSpaceQuotientToAdeleBddQuotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hdimL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := K)
      ((LSpace D₁).comap (LSpace D₂).subtype)
    rw [← hℓ₁] at h; exact h.symm
  have hdimB : ell D₂ = finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) + ell D₁ := by
    rw [← hran, LinearMap.finrank_range_of_inj
      (lSpaceQuotientToAdeleBddQuotient_injective hD)]
    exact hdimL
  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  have hfinB : Module.Finite K (adeleBdd D₂ ⧸ B) := Module.Finite.equiv e3
  have hdim2 : finrank K (adeleBdd D₂ ⧸ A)
      = finrank K (adeleBdd D₂ ⧸ B) + finrank K (B.map A.mkQ : Submodule K _) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := adeleBdd D₂ ⧸ A)
      (B.map A.mkQ)
    rw [LinearEquiv.finrank_eq e3] at h; omega
  have e2 := LinearMap.quotientInfEquivSupQuotient (R := K)
    (adeleBdd D₂) (adeleBdd D₁ ⊔ globalSub K F)
  have hsup : adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F) = adeleBdd D₂ ⊔ globalSub K F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleBdd_mono hD)]
  have hB' : (adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype = B := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  let eL : (adeleBdd D₂ ⧸ B) ≃ₗ[K]
      (adeleBdd D₂ ⧸ ((adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
        (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype)) :=
    Submodule.quotEquivOfEq _ _ hB'.symm
  have hfin_iso : Module.Finite K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype) :=
    Module.Finite.equiv (eL.trans e2)
  have hdim_iso : finrank K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype)
      = finrank K (adeleBdd D₂ ⧸ B) :=
    (LinearEquiv.finrank_eq (eL.trans e2)).symm
  have hcast : (finrank K (adeleBdd D₂ ⧸ A) : ℤ)
      = (finrank K (adeleBdd D₂ ⧸ B) : ℤ) + ((ell D₂ : ℤ) - (ell D₁ : ℤ)) := by
    have hb : (ell D₂ : ℤ)
        = (finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) : ℤ) + (ell D₁ : ℤ) := by
      exact_mod_cast hdimB
    push_cast [hdim2]; linarith
  have hgoal : (finrank K (adeleBdd D₂ ⧸ B) : ℤ)
      = Divisor.degree D₂ - ↑(ell D₂) - (Divisor.degree D₁ - ↑(ell D₁)) := by
    linarith [hdimA, hcast]
  clear_value eL
  exact hsup ▸ ⟨hfin_iso, by rw [hdim_iso]; exact hgoal⟩

section Index

variable [IsCurveOver K F] [Nonempty (Place K F)]

theorem adeleBddSup_eq_of_degree_sub_ell_eq {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim
  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  have := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

end Index

namespace RiemannGenusReachedAt
open _root_.AlgebraicCurve.RiemannGenusReachedAt
end RiemannGenusReachedAt
namespace RiemannGenusReachedAt
open scoped _root_.AlgebraicCurve.RiemannGenusReachedAt in
private theorem _root_.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  have := finiteDimensional_lSpace (K := K) D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree (K := K) hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end RiemannGenusReachedAt
open _root_.AlgebraicCurve

theorem adeleSpace_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F := by
  refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace D₀)
  rw [adeleSpace, iSup_le_iff]
  intro D
  refine le_trans (adeleBdd_mono (le_sup_left : D ≤ D ⊔ D₀)) ?_
  have := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heq : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = Divisor.degree D₀ - ell D₀ :=
    (h.eq_of_ge le_sup_right).trans h.eq.symm
  have hsup := adeleBddSup_eq_of_degree_sub_ell_eq (K := K)
    (le_sup_right : D₀ ≤ D ⊔ D₀) heq
  rw [← hsup]
  exact le_sup_left

theorem indexOfSpecialty_eq_zero_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    indexOfSpecialty D₀ = 0 := by
  rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap, ← adeleSpace_eq_of_genusReached h,
    Submodule.comap_subtype_self]
  have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton


theorem finite_adele_quotient_and_index_formula_of_genusReached
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  classical
  have hDD' : D ≤ D ⊔ D₀ := le_sup_left
  have hD0D' : D₀ ≤ D ⊔ D₀ := le_sup_right
  have := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heqD' : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = γ - 1 := h.eq_of_ge hD0D'
  have hsa : adeleSpace K F = adeleBdd (D ⊔ D₀) ⊔ globalSub K F := by
    refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace _)
    rw [adeleSpace_eq_of_genusReached h]
    exact sup_le_sup_right (adeleBdd_mono hD0D') _
  have hABsub : adeleBdd D ⊔ globalSub K F ≤ adeleBdd (D ⊔ D₀) ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hDD') _
  have hBCsub : adeleBdd (D ⊔ D₀) ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _
  have hCB : (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype = ⊤ := by
    rw [← hsa, Submodule.comap_subtype_self]
  have hfinCB : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [hCB]
    have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  have hdimCB : finrank K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) = 0 := by
    rw [hCB]
    have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hDD'
  have := hfinBA
  obtain ⟨hfinCA, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D ⊔ globalSub K F) (B := adeleBdd (D ⊔ D₀) ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  have hieq : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  rw [adeleBddPrincipal_eq_comap]
  refine ⟨hfinCA, ?_⟩
  rw [hieq]
  push_cast [hdimCA, hdimCB]
  linarith [hdimBA, heqD']

theorem gate_indexOfSpecialty_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  have h1 := (finite_adele_quotient_and_index_formula_of_genusReached h D₀).2
  have h2 := h.eq
  have h3 := indexOfSpecialty_eq_zero_of_genusReached h
  exact_mod_cast h3

theorem gate_riemannInequality_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have heq := (finite_adele_quotient_and_index_formula_of_genusReached h D).2
  have hnn : (0 : ℤ) ≤ indexOfSpecialty D := Int.natCast_nonneg _
  linarith

end AlgebraicCurve

end

open _root_.AlgebraicCurve in
theorem _root_.AlgebraicCurve.indexOfSpecialty_eq_of_genusReached
    {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) :=
  AlgebraicCurve.finite_adele_quotient_and_index_formula_of_genusReached (K := K) (F := F)
    (γ := γ) (D₀ := D₀) (h := h) (D := D)
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.IndexOfSpecialty_eq_of_genusReached
end ProofImplementation

end

section

/-! # Finite dimension of Riemann spaces -/

open AlgebraicCurves.Cohomology.RiemannRoch.Proofs

namespace AlgebraicCurve

theorem finiteDimensional_lSpace
    {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [hL0 : FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K ↥(LSpace D) :=
  IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve.finiteDimensional_lSpace
    (K := K) D

end AlgebraicCurve

end

section

/-! # Bounding the change of Riemann space dimension -/

open AlgebraicCurves.Cohomology.RiemannRoch.Proofs

namespace AlgebraicCurve

theorem ell_sub_ell_le_degree_sub_degree {K F : Type*} [Field K] [Field F]
  [Algebra K F] [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K ↥(LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ :=
  IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree
    (K := K) hD

end AlgebraicCurve

end

section

/-! # Finite dimension of differential spaces after genus attainment -/

namespace AlgebraicCurve

theorem omegaSpace_finite_of_genusReached {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 :
    Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K ↥(omegaSpace (K := K) (F := F) D) := by
  have := (indexOfSpecialty_eq_of_genusReached h D).1
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

end AlgebraicCurve

end

section

/-! Derive the Riemann index formula from attainment of the Riemann genus. -/

namespace AlgebraicCurve

theorem riemannIndexFormula_of_genusReached {K : Type*} {F : Type*} [Field
  K] [Field F] [Algebra K F]
    (hg : ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
      RiemannGenusReached K F (genus K F)) :
    RiemannIndexFormula K F := by
  intro _ _ D
  obtain ⟨hne, hL0, D₀, hD₀⟩ := hg
  have := hne
  have := hL0
  exact (indexOfSpecialty_eq_of_genusReached hD₀ D).2

end AlgebraicCurve

end

section

/-! # The adele quotient after the genus is attained -/

open AlgebraicCurves.Cohomology.RiemannRoch.Proofs

namespace AlgebraicCurve

theorem adeleSpace_eq_of_genusReached
    {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F :=
  IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve.adeleSpace_eq_of_genusReached
    (K := K) h

end AlgebraicCurve

end

section

/-! # The genus formula for the adelic Riemann index -/

namespace AlgebraicCurve

theorem exists_genus_riemannIndex_of_stichtenothGenusExists {K F : Type*}
    [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) :
    ∃ γ : ℤ, ∀ D : Divisor K F,
      Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  obtain ⟨hne, hfin, γ, D₀, hγ⟩ := h
  have := hne
  have := hfin
  exact ⟨γ, fun D => indexOfSpecialty_eq_of_genusReached hγ D⟩

end AlgebraicCurve

end

section

/-! # Attainment of a bounded Riemann genus -/

namespace AlgebraicCurve

theorem exists_riemannGenusReachedAt_of_bounded {K F : Type*} [Field K]
  [Field F] [Algebra K F] [IsCurveOver K F] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨γ, hγ⟩ := hbdd
  obtain ⟨M, ⟨D₀, hD₀⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n => ∃ D : Divisor K F, Divisor.degree D - ell D = n)
      ⟨γ, fun n ⟨D, hD⟩ => hD ▸ hγ D⟩
      ⟨Divisor.degree (0 : Divisor K F) - ell (0 : Divisor K F), 0, rfl⟩
  refine ⟨M + 1, D₀, ?_, ?_, ?_⟩
  · exact finiteDimensional_lSpace D₀
  · rw [hD₀]; ring
  · intro D
    have := hMmax (Divisor.degree D - ell D) ⟨D, rfl⟩
    linarith

end AlgebraicCurve

end

section

/-! The index of specialty vanishes at a divisor attaining the Riemann genus. -/

namespace AlgebraicCurve

theorem indexOfSpecialty_eq_zero_of_genusReached {K F : Type*} [Field K]
  [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace
  (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    indexOfSpecialty D₀ = 0 := by
  have hspace := adeleSpace_eq_of_genusReached h
  have hglobal : globalSub K F ≤ adeleSpace K F := by
    rw [hspace]
    exact le_sup_right
  have hprincipal : adeleBddPrincipal K F D₀ = ⊤ := by
    apply Submodule.map_injective_of_injective (f := (adeleSpace K F).subtype)
      (adeleSpace K F).subtype_injective
    rw [adeleBddPrincipal, Submodule.map_sup, Submodule.map_comap_subtype,
      Submodule.map_comap_subtype, Submodule.map_top, Submodule.range_subtype,
      inf_eq_right.mpr adeleBdd_le_adeleSpace, inf_eq_right.mpr hglobal]
    exact hspace.symm
  rw [indexOfSpecialty_eq, hprincipal]
  have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

end AlgebraicCurve

end
