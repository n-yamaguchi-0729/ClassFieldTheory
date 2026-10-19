/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.MulMemLSpaceAdd
import Nyll.AlgebraicCurves.Divisors.Degree.PoleData
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.FunctionFields.Rational.TranscendenceTowerPoleDivisorApply
import Nyll.AlgebraicCurves.FunctionFields.Rational.TranscendenceTowerDegreePoleDivisorEqFinrank
import Nyll.AlgebraicCurves.FunctionFields.LinearAlgebra.LinearIndependentPowMul
import Nyll.AlgebraicCurves.FunctionFields.LinearAlgebra.LinearIndependentPowTranscendental
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

/-! Integral bases and pole divisors give existence of the genus
for a finite rational-function tower. -/

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFieldStichtenothRatFunc

open Polynomial IsLocalRing
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs
open IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem stichtenothGenusExists_of_bounded
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    StichtenothGenusExists K F :=
  ⟨‹_›, ‹_›, exists_riemannGenusReachedAt_of_bounded hbdd⟩


theorem indexOfSpecialtyFinite_of_stichtenothGenusExists
    [IsCurveOver K F] (hSG : StichtenothGenusExists K F) :
    IndexOfSpecialtyFinite K F := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := hSG
  have : Nonempty (Place K F) := hne
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hL0
  exact ⟨D₀, (_root_.AlgebraicCurve.indexOfSpecialty_eq_of_genusReached hD₀ D₀).1⟩

end AlgebraicCurve

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve hiding Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem pow_mem_lSpace_nsmul {B : Divisor K F} {f : F} (hf : f ∈ LSpace B) (j : ℕ) :
    f ^ j ∈ LSpace (j • B) := by
  induction j with
  | zero => simpa only [pow_zero, zero_nsmul] using one_mem_lSpace_zero (K := K) (F := F)
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace_add ih hf

namespace PoleDivisorPackage
open _root_.AlgebraicCurve.PoleDivisorPackage
open _root_.AlgebraicCurve.PoleDivisorPackage

variable (P : PoleDivisorPackage K F)

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.pow_mul_u_mem_lSpace (j : ℕ) (i : Fin
  P.n) :
    P.x ^ j * P.u i ∈ LSpace ((j + P.c) • P.B) := by
  rw [add_nsmul]
  exact mul_mem_lSpace_add (pow_mem_lSpace_nsmul P.hx_mem j) (P.hu_mem i)

open _root_.AlgebraicCurve.PoleDivisorPackage

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.pow_mul_u_mem_lSpace_of_le {j m : ℕ} (hjm
  : j + P.c ≤ m) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace (m • P.B) := by
  refine lSpace_mono ?_ (P.pow_mul_u_mem_lSpace j i)
  intro v
  have hBv : (0 : ℤ) ≤ P.B v := P.hB_eff v
  change ((j + P.c) • P.B) v ≤ (m • P.B) v
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hBv

open _root_.AlgebraicCurve.PoleDivisorPackage

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.ell_nsmul_poleDivisor_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    (P.n : ℤ) * (m - P.c + 1) ≤ ell (m • P.B) := by
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) (m • P.B)
  set g : Fin (m - P.c + 1) × Fin P.n → LSpace (m • P.B) :=
    fun p => ⟨P.x ^ (p.1 : ℕ) * P.u p.2,
      P.pow_mul_u_mem_lSpace_of_le (by have := p.1.isLt; omega) p.2⟩
    with hgdef
  have hsub : LinearIndependent K (fun p => (g p : F)) := by
    have heq : (fun p => (g p : F))
        = (fun p : ℕ × Fin P.n => P.x ^ p.1 * P.u p.2)
            ∘ (fun p : Fin (m - P.c + 1) × Fin P.n => ((p.1 : ℕ), p.2)) := by
      funext p; rfl
    rw [heq]
    refine P.lin_indep.comp _ ?_
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.val_injective hpq.1) hpq.2
  have hg : LinearIndependent K g := hsub.of_comp (LSpace (m • P.B)).subtype
  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hZ : ((m - P.c + 1) * P.n : ℤ) ≤ (ell (m • P.B) : ℤ) := by exact_mod_cast hcard
  have heq : (((m - P.c + 1 : ℕ) : ℤ) * P.n : ℤ) = (P.n : ℤ) * ((m : ℤ) - P.c + 1) := by
    rw [Nat.cast_add, Nat.cast_sub hm, Nat.cast_one]; ring
  linarith

open _root_.AlgebraicCurve.PoleDivisorPackage

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.degree_nsmul_sub_ell_le [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    Divisor.degree (m • P.B) - ell (m • P.B) ≤ (P.n : ℤ) * (P.c - 1) := by
  have hge := P.ell_nsmul_poleDivisor_ge hm
  have hdeg : Divisor.degree (m • P.B) = (m : ℤ) * P.n := by
    rw [show m • P.B = (m : ℤ) • P.B from (natCast_zsmul _ _).symm,
      Divisor.degree.map_zsmul, smul_eq_mul, P.degB_eq]
  linarith

open _root_.AlgebraicCurve.PoleDivisorPackage
end PoleDivisorPackage

namespace PoleDivisorPackage
open _root_.AlgebraicCurve.PoleDivisorPackage
end PoleDivisorPackage
namespace PoleDivisorPackage
open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
private theorem _root_.AlgebraicCurve.PoleDivisorPackage.ell_nsmul_sub_pos [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) {A : Divisor K F} (hA : 0 ≤ A) {m : ℕ} (hm : P.c ≤ m)
    (hbig : Divisor.degree A < (P.n : ℤ) * (m - P.c + 1)) :
    0 < ell (m • P.B - A) := by
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) (m • P.B)
  have hle : m • P.B - A ≤ m • P.B := by
    intro v
    have hAv : (0 : ℤ) ≤ A v := hA v
    rw [Finsupp.sub_apply]
    linarith
  have h48 := _root_.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree (K := K) hle
  rw [map_sub, sub_sub_cancel] at h48
  have h412 := P.ell_nsmul_poleDivisor_ge hm
  have : (0 : ℤ) < (ell (m • P.B - A) : ℤ) := by linarith
  exact_mod_cast this

end PoleDivisorPackage
open _root_.AlgebraicCurve
namespace PoleDivisorPackage
open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
private theorem _root_.AlgebraicCurve.PoleDivisorPackage.degree_sub_ell_le [IsCurveOver K F]
  [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (P.n : ℤ) * (P.c - 1) := by
  classical
  set D' : Divisor K F := D ⊔ 0 with hD'def
  have hD'eff : 0 ≤ D' := le_sup_right
  have hDD' : D ≤ D' := le_sup_left
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) D'
  have hmono : Divisor.degree D - (ell D : ℤ) ≤ Divisor.degree D' - ell D' := by
    have h := _root_.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree (K := K) hDD'
    linarith
  set m : ℕ := P.c + (Divisor.degree D').toNat with hmdef
  have hcm : P.c ≤ m := Nat.le_add_right _ _
  have hdegD' : 0 ≤ Divisor.degree D' := Divisor.degree_nonneg_of_nonneg hD'eff
  have hbig : Divisor.degree D' < (P.n : ℤ) * (m - P.c + 1) := by
    have hcast : ((m : ℤ) - P.c) = Divisor.degree D' := by
      simp only [hmdef, Nat.cast_add, add_sub_cancel_left, Int.toNat_of_nonneg hdegD']
    rw [hcast]
    have hn1 : (1 : ℤ) ≤ P.n := by exact_mod_cast P.hn_pos
    nlinarith
  have hellpos := P.ell_nsmul_sub_pos hD'eff hcm hbig
  have hnebot : LSpace (m • P.B - D') ≠ ⊥ :=
    fun h => by rw [ell, h, finrank_bot] at hellpos; exact lt_irrefl 0 hellpos
  obtain ⟨z, hzL, hz0⟩ := (Submodule.ne_bot_iff _).mp hnebot
  obtain ⟨Dz, hDzord, hDzdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzmem := (mem_lSpace_iff_ord.mp hzL).resolve_left hz0
  have hD'le : D' ≤ m • P.B + Dz := by
    intro v
    have := hzmem v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, neg_sub] at this ⊢
    rw [hDzord]; linarith
  have hellshift : ell (m • P.B + Dz) = ell (m • P.B) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • P.B) hz0 hDzord)).symm
  have hdegshift : Divisor.degree (m • P.B + Dz) = Divisor.degree (m • P.B) := by
    rw [map_add, hDzdeg, add_zero]
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) (m • P.B + Dz)
  have hmono' : Divisor.degree D' - (ell D' : ℤ)
      ≤ Divisor.degree (m • P.B + Dz) - ell (m • P.B + Dz) := by
    have h := _root_.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree (K := K) hD'le
    linarith
  rw [hellshift, hdegshift] at hmono'
  have h412 := P.degree_nsmul_sub_ell_le hcm
  linarith

end PoleDivisorPackage
open _root_.AlgebraicCurve

theorem riemannGenusBounded_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    RiemannGenusBounded K F :=
  ⟨(P.n : ℤ) * (P.c - 1), P.degree_sub_ell_le⟩

theorem stichtenothGenusExists_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_poleDivisorPackage P)

theorem indexOfSpecialtyFinite_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists
    (stichtenothGenusExists_of_poleDivisorPackage P)

theorem indexOfSpecialtyFinite_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage h.some

theorem stichtenothGenusExists_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage h.some


end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve hiding Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

namespace TranscendenceTower
open _root_.AlgebraicCurve.TranscendenceTower
open _root_.AlgebraicCurve.TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
variable (T : TranscendenceTower K E F)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.x_ne_zero : T.x ≠ 0 := fun h => by
  have := T.hxv; rw [h, Place.ord_zero] at this; exact absurd this (by decide)

open _root_.AlgebraicCurve.TranscendenceTower
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
theorem xF_ne_zero : T.xF ≠ 0 :=
  fun h => T.x_ne_zero ((algebraMap E F).injective (by rwa [map_zero]))

open _root_.AlgebraicCurve.TranscendenceTower
omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.poleDivisor_nonneg : 0 ≤ T.poleDivisor
  := by
  classical
  intro w
  rw [Finsupp.coe_zero, Pi.zero_apply, T.poleDivisor_apply, Finsupp.single_apply]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  split_ifs <;> omega

open _root_.AlgebraicCurve.TranscendenceTower
omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.xF_mem_lSpace_poleDivisor : T.xF ∈ LSpace
  T.poleDivisor := by
  classical
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [T.poleDivisor_apply, Place.ord_restrict, Finsupp.single_apply]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, T.hxv, ite_true, mul_one, mul_neg_one, le_refl]
  · simp only [ite_eq_right (Ne.symm hw), mul_zero, neg_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

open _root_.AlgebraicCurve.TranscendenceTower

open _root_.AlgebraicCurve.TranscendenceTower
omit [FiniteDimensional E F] in
private theorem
  _root_.AlgebraicCurve.TranscendenceTower.mem_lSpace_nsmul_poleDivisor_of_regular_outside {f : F}
    (hreg : ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f)
    {c : ℕ} (hc : ∀ w ∈ T.v.fiber F, -(c : ℤ) ≤ w.ord f) :
    f ∈ LSpace (c • T.poleDivisor) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [Finsupp.smul_apply, T.poleDivisor_apply, Finsupp.single_apply, nsmul_eq_mul]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, ite_true, mul_one]
    have he : (1 : ℤ) ≤ w.ramificationIndex E := by
      exact_mod_cast w.ramificationIndex_pos (F := E)
    have hbdd := hc w (Place.mem_fiber.mpr hw)
    nlinarith [Int.natCast_nonneg c]
  · simp only [ite_eq_right (Ne.symm hw), mul_zero, neg_zero]
    exact hreg w hw

open _root_.AlgebraicCurve.TranscendenceTower
omit [FiniteDimensional E F] in
private theorem
  _root_.AlgebraicCurve.TranscendenceTower.exists_forall_mem_lSpace_nsmul_poleDivisor {n : ℕ} (u :
  Fin n → F)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • T.poleDivisor) := by
  classical
  refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
    (T.v.fiber F).sup fun w => (-(w.ord (u i))).toNat,
    fun i => T.mem_lSpace_nsmul_poleDivisor_of_regular_outside (hreg i) ?_⟩
  intro w hw
  have h1 : (-(w.ord (u i))).toNat
      ≤ (T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat :=
    Finset.le_sup (f := fun w' => (-(w'.ord (u i))).toNat) hw
  have h2 : ((T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat)
      ≤ (Finset.univ : Finset (Fin n)).sup fun i' =>
          (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat :=
    Finset.le_sup (f := fun i' => (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat)
      (Finset.mem_univ i)
  have htnat : -(w.ord (u i)) ≤ ((-(w.ord (u i))).toNat : ℤ) := Int.self_le_toNat _
  omega

open _root_.AlgebraicCurve.TranscendenceTower
end TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F]

section PrincipalDivisors
variable [HasPrincipalDivisors K F]

namespace IntegralBasisInLSpace
open _root_.AlgebraicCurve.IntegralBasisInLSpace
end IntegralBasisInLSpace
open scoped _root_.AlgebraicCurve.IntegralBasisInLSpace in
/-- The integral-basis package built from a basis regular away from the tower place. -/
def IntegralBasisInLSpace.ofRegularOutside (T : TranscendenceTower K E F)
    (u : Fin (Module.finrank E F) → F) (hu_indep : LinearIndependent E u)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    IntegralBasisInLSpace T where
  c := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose
  u := u
  hu_indep := hu_indep
  hu_mem := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose_spec

omit [FiniteDimensional E F] in
theorem hasIntegralBasisInLSpace_of_regularOutside (T : TranscendenceTower K E F)
    (h : HasIntegralBasisRegularOutside K E F T) :
    HasIntegralBasisInLSpace K E F T := by
  obtain ⟨u, hu_indep, hreg⟩ := h
  exact ⟨IntegralBasisInLSpace.ofRegularOutside T u hu_indep hreg⟩

open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
/-- The pole-divisor data obtained from a transcendence tower and its integral basis. -/
def PoleDivisorPackage.ofTranscendenceTower (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    PoleDivisorPackage K F where
  x := T.xF
  B := T.poleDivisor
  hB_eff := T.poleDivisor_nonneg
  hx_mem := T.xF_mem_lSpace_poleDivisor
  n := Module.finrank E F
  hn_pos := Module.finrank_pos
  degB_eq := T.degree_poleDivisor_eq_finrank
  c := IB.c
  u := IB.u
  hu_mem := IB.hu_mem
  lin_indep := linearIndependent_pow_mul T.hx_indep IB.hu_indep

theorem hasPoleDivisorPackage_of_transcendenceTower
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    HasPoleDivisorPackage K F :=
  ⟨PoleDivisorPackage.ofTranscendenceTower T IB⟩

theorem hasPoleDivisorPackage_of_hasIntegralBasisInLSpace
    (T : TranscendenceTower K E F) (h : HasIntegralBasisInLSpace K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_transcendenceTower T h.some

theorem hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside
    (T : TranscendenceTower K E F) (h : HasIntegralBasisRegularOutside K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisInLSpace T
    (hasIntegralBasisInLSpace_of_regularOutside T h)

end PrincipalDivisors

theorem indexOfSpecialtyFinite_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

theorem stichtenothGenusExists_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)


end AlgebraicCurve

end

noncomputable section

open Module

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve hiding Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg mem_iff_ord_nonneg
  restrict_placeOfPrime placeOfPrime

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral {f : F} (hf : IsIntegral
  w.toValuationSubring f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hf
  exact hy ▸ y.2

open _root_.AlgebraicCurve.Place

theorem ord_nonneg_of_isIntegral {f : F} (hf : IsIntegral w.toValuationSubring f) :
    0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral hf)

private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem {A : Type*}
  [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by
  let : Algebra A w.toValuationSubring :=
    ((algebraMap A F).codRestrict w.toValuationSubring.toSubring hA).toAlgebra
  have : IsScalarTower A w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  exact w.mem_of_isIntegral hf.tower_top

open _root_.AlgebraicCurve.Place

theorem ord_nonneg_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_algebraMap_mem hA hf)

end Place

section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place
open _root_.AlgebraicCurve.Place
end Place
namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict [Algebra.IsIntegral E F]
  (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by
  refine w.mem_of_isIntegral_of_algebraMap_mem (fun a => ?_) hf
  rw [IsScalarTower.algebraMap_apply A E F, ← w.mem_restrict_iff, hw]
  exact hA a

end Place
open _root_.AlgebraicCurve
namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict
  [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_restrict hw hA hf)

end Place
open _root_.AlgebraicCurve
namespace TranscendenceTower
open _root_.AlgebraicCurve.TranscendenceTower
end TranscendenceTower
namespace TranscendenceTower
open scoped _root_.AlgebraicCurve.TranscendenceTower in
private theorem _root_.AlgebraicCurve.TranscendenceTower.ord_nonneg_of_isIntegral_of_regularOutside
    [Algebra.IsIntegral E F] (T : TranscendenceTower K E F) (hA : T.RegularOutside A)
    {f : F} (hf : IsIntegral A f) :
    ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f := fun w hw =>
  w.ord_nonneg_of_isIntegral_of_restrict rfl (hA _ hw) hf

end TranscendenceTower
open _root_.AlgebraicCurve
end Bridge

section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in
theorem linearIndependent_reindex_basis {s : Finset F} (b : Basis s E F) :
    LinearIndependent E (fun i : Fin (Module.finrank E F) =>
      b ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm i)) :=
  b.linearIndependent.comp _ (Equiv.injective _)

omit [HasPrincipalDivisors K F] in
theorem hasIntegralBasisRegularOutside_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F
  set e : Fin (Module.finrank E F) ≃ s :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨fun i => b (e i), linearIndependent_reindex_basis b, fun i w hw => ?_⟩
  exact T.ord_nonneg_of_isIntegral_of_regularOutside hA (hint (e i)) w hw

omit [HasPrincipalDivisors K F] in
theorem hasIntegralBasisRegularOutside_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨A, hfrac, hreg⟩ := h
  have : IsFractionRing A E := hfrac
  exact hasIntegralBasisRegularOutside_of_isFractionRing (A := A) T
    (fun u hu a => hreg u hu (a : E) a.property)

theorem hasPoleDivisorPackage_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_isFractionRing T hA)

omit [HasPrincipalDivisors K F] in
theorem stichtenothGenusExists_of_isFractionRing [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_isFractionRing T hA)

theorem hasPoleDivisorPackage_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T h)

omit [HasPrincipalDivisors K F] in
theorem stichtenothGenusExists_of_hasRegularFractionSubring [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_hasRegularFractionSubring T h)

namespace TranscendenceTower
open scoped _root_.AlgebraicCurve.TranscendenceTower in
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.adjoin_x_regularOutside (T :
  TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v →
      ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ u.toValuationSubring := by
  intro u hu a ha
  let S : Subalgebra K E :=
    { u.toValuationSubring.toSubsemiring with
      algebraMap_mem' := u.algebraMap_mem' }
  suffices h : a ∈ S from h
  refine Algebra.adjoin_le ?_ ha
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  change T.x ∈ u.toValuationSubring
  exact u.mem_of_ord_nonneg T.x_ne_zero (T.hxreg u hu)

end TranscendenceTower
open _root_.AlgebraicCurve
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
theorem hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasRegularFractionSubring K E F T :=
  ⟨Algebra.adjoin K {T.x}, hfrac, T.adjoin_x_regularOutside⟩

omit [HasPrincipalDivisors K F] in
theorem hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasIntegralBasisRegularOutside K E F T :=
  hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

omit [HasPrincipalDivisors K F] in
theorem stichtenothGenusExists_of_adjoin_x_isFractionRing [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

end Headline

end AlgebraicCurve

end

noncomputable section

open Module Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

/-- The rational-function-field tower with the standard variable and the place at infinity. -/
def transcendenceTower : TranscendenceTower K (RatFunc K) F where
  x := RatFunc.X
  hx_indep := linearIndependent_pow_of_transcendental RatFunc.transcendental_X
  v := placeInfty K
  hvdeg := deg_placeInfty K
  hxv := ord_placeInfty_X K
  hxreg := fun _ hu => ord_X_nonneg_of_ne_placeInfty K hu
omit [DecidableEq (RatFunc K)] in
theorem aeval_X_eq_algebraMap (q : K[X]) :
    (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K)) q
      = algebraMap K[X] (RatFunc K) q := by
  have hext : (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K))
      = IsScalarTower.toAlgHom K K[X] (RatFunc K) :=
    Polynomial.algHom_ext (by
      change Polynomial.aeval (RatFunc.X : RatFunc K) Polynomial.X =
        algebraMap K[X] (RatFunc K) Polynomial.X
      rw [Polynomial.aeval_X, RatFunc.algebraMap_X])
  rw [hext]; rfl

omit [DecidableEq (RatFunc K)] in
theorem algebraMap_polynomial_mem_adjoin_X (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Algebra.adjoin K {(RatFunc.X : RatFunc K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, aeval_X_eq_algebraMap K q⟩

omit [DecidableEq (RatFunc K)] in
theorem isFractionRing_adjoin_X :
    IsFractionRing (Algebra.adjoin K {(RatFunc.X : RatFunc K)}) (RatFunc K) := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  refine ⟨⟨algebraMap K[X] (RatFunc K) z.num, algebraMap_polynomial_mem_adjoin_X K z.num⟩,
    ⟨algebraMap K[X] (RatFunc K) z.denom, algebraMap_polynomial_mem_adjoin_X K z.denom⟩, ?_⟩
  change z = algebraMap K[X] (RatFunc K) z.num / algebraMap K[X] (RatFunc K) z.denom
  exact z.num_div_denom.symm

theorem hasRegularFractionSubring :
    HasRegularFractionSubring K (RatFunc K) F (transcendenceTower K F) :=
  hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

theorem hasIntegralBasisRegularOutside :
    HasIntegralBasisRegularOutside K (RatFunc K) F (transcendenceTower K F) :=
  hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [HasPrincipalDivisors K F]

omit [DecidableEq (RatFunc K)] in
theorem hasPoleDivisorPackage_of_ratFunc_tower :
    HasPoleDivisorPackage K F := open scoped Classical in
  hasPoleDivisorPackage_of_hasRegularFractionSubring
    (transcendenceTower K F) (hasRegularFractionSubring K F)

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

omit [HasPrincipalDivisors K F] in
omit [DecidableEq (RatFunc K)] in
theorem stichtenothGenusExists_of_finite_separable_ratFunc :
    StichtenothGenusExists K F := open scoped Classical in
  stichtenothGenusExists_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

end RationalFunctionField
end AlgebraicCurve

end

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower (K :
  Type*) [Field K] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K
  (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
  [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    StichtenothGenusExists K F := by
  classical
  exact AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_finite_separable_ratFunc K F

end AlgebraicCurves.Places.Rational.Proofs.RationalFieldStichtenothRatFunc
