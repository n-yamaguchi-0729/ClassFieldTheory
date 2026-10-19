/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finite ramification in a separable extension

A primitive element gives a nonzero minimal-polynomial derivative. Outside the support of
that derivative and the poles of the coefficients, the derivative belongs to the different
but not to the centre of the place. The different therefore rules out ramification.
This argument allows wild ramification and does not divide by the ramification index.
-/

noncomputable section

open Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- At a place where a primitive element has integral minimal-polynomial coefficients and
unit derivative, the ramification index is one. No tameness assumption is needed. -/
theorem ramificationIndex_eq_one_of_minpoly_derivative_unit
    (w : Place K F') (x : F') (hx : Algebra.adjoin F {x} = ⊤)
    (hcoeff : ∀ i, (minpoly F x).coeff i ∈ (w.restrict F).toValuationSubring)
    (hderiv : w.ord (aeval x (derivative (minpoly F x))) = 0) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let : Algebra A F' := valuationSubringAlgebra F' v
  have : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let B := integralClosureAt F' v
  have : IsScalarTower A B F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure B A F' := integralClosure.isIntegralClosure A F'
  have hxint : IsIntegral A x := by
    have hlift : minpoly F x ∈ lifts (algebraMap A F) := by
      rw [lifts_iff_coeff_lifts]
      exact fun i => ⟨⟨(minpoly F x).coeff i, hcoeff i⟩, rfl⟩
    obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_degree_eq_and_monic hlift
      (minpoly.monic (Algebra.IsIntegral.isIntegral x : IsIntegral F x))
    refine ⟨Q, hQmonic, ?_⟩
    change aeval x Q = 0
    rw [← aeval_map_algebraMap F, hQmap, minpoly.aeval]
  let b : B := ⟨x, hxint⟩
  let d : B := aeval b (derivative (minpoly A b))
  have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A F' b
  have hdimage : algebraMap B F' d = aeval x (derivative (minpoly F x)) := by
    change algebraMap B F' (aeval b (derivative (minpoly A b))) =
      aeval (algebraMap B F' b) (derivative (minpoly F (algebraMap B F' b)))
    rw [minpoly.isIntegrallyClosed_eq_field_fractions F F' hbint,
      derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply]
  have hdzero : d ≠ 0 := by
    intro hd
    have hne : aeval x (derivative (minpoly F x)) ≠ 0 :=
      (Algebra.IsSeparable.isSeparable F x).aeval_derivative_ne_zero (minpoly.aeval F x)
    apply hne
    rw [← hdimage, hd, map_zero]
  have hddiff : d ∈ differentIdeal A B :=
    aeval_derivative_mem_differentIdeal A F F' b hx
  let P := (fiberCenter F' v (rfl : w.restrict F = v)).asIdeal
  have hdnot : d ∉ P := by
    intro hd
    have hpos := (mem_fiberCenter_iff_ord_pos (rfl : w.restrict F = v) hdzero).mp hd
    rw [hdimage, hderiv] at hpos
    exact (lt_irrefl 0) hpos
  have hram := ramificationIndex_eq_ramificationIdx_fiberCenter v
    (rfl : w.restrict F = v)
  have hepos := w.ramificationIndex_pos (F := F)
  by_contra he
  have he2 : 2 ≤ (IsLocalRing.maximalIdeal A).ramificationIdx' P := by
    change w.ramificationIndex F =
      (IsLocalRing.maximalIdeal A).ramificationIdx' P at hram
    omega
  have hP2 : P ^ 2 ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.le_pow_of_le_ramificationIdx'
      (p := IsLocalRing.maximalIdeal A) (P := P) he2)
  have hPdiff : P ∣ differentIdeal A B := by
    simpa only [Nat.reduceSub, pow_one] using pow_sub_one_dvd_differentIdeal_aux A F F' P
      (e := 2) (by decide) (maximalIdeal_ne_bot v) hP2
  exact hdnot ((Ideal.dvd_iff_le.mp hPdiff) hddiff)

end Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']

private theorem finite_ord_support (x : F') :
    {w : Place K F' | w.ord x ≠ 0}.Finite := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Place.ord_zero, ne_eq, not_true_eq_false, Set.ofPred_false, Set.finite_empty]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  exact D.support.finite_toSet.subset (fun w hw => by
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff, hD w, Set.mem_ofPred_eq] using hw)

/-- A finite separable extension has only finitely many ramified places, including in positive
characteristic when some of the ramification is wild. -/
theorem finite_setOf_ramificationIndex_ne_one :
    {w : Place K F' | w.ramificationIndex F ≠ 1}.Finite := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F F'
  let x := pb.gen
  let p := minpoly F x
  let d := aeval x (derivative p)
  let S : Set (Place K F') := {w | w.ord d ≠ 0} ∪
    ⋃ i ∈ (p.support : Set ℕ), {w | w.ord (algebraMap F F' (p.coeff i)) ≠ 0}
  have hS : S.Finite := (finite_ord_support d).union
    (p.support.finite_toSet.biUnion (fun i _ => finite_ord_support _))
  refine hS.subset ?_
  intro w hw
  by_contra hwS
  have hd : w.ord d = 0 := by
    by_contra hd
    exact hwS (Or.inl hd)
  have hc : ∀ i, p.coeff i ∈ (w.restrict F).toValuationSubring := by
    intro i
    by_cases hi : p.coeff i = 0
    · rw [hi]
      exact zero_mem _
    have hni : i ∈ p.support := mem_support_iff.mpr hi
    have hord : w.ord (algebraMap F F' (p.coeff i)) = 0 := by
      by_contra hord
      exact hwS (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hni, hord⟩⟩))
    change algebraMap F F' (p.coeff i) ∈ w.toValuationSubring
    have hne : algebraMap F F' (p.coeff i) ≠ 0 := by
      simpa only [map_zero] using (algebraMap F F').injective.ne_iff.mpr hi
    exact (w.mem_iff_ord_nonneg hne).mpr (by rw [hord])
  exact hw (w.ramificationIndex_eq_one_of_minpoly_derivative_unit x
    pb.adjoin_gen_eq_top hc hd)

/-- A finite set outside which every ramification index is one, without a tameness hypothesis. -/
theorem exists_finset_forall_not_mem_ramificationIndex_eq_one_of_isSeparable :
    ∃ S : Finset (Place K F'), ∀ w, w ∉ S → w.ramificationIndex F = 1 := by
  classical
  refine ⟨(finite_setOf_ramificationIndex_ne_one (K := K) (F := F) (F' := F')).toFinset, ?_⟩
  intro w hw
  simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hw

/-- The exceptional set can be chosen on the base: every place above a base place outside
this finite set has ramification index one. -/
theorem exists_finset_forall_restrict_not_mem_ramificationIndex_eq_one_of_isSeparable :
    ∃ S : Finset (Place K F), ∀ w : Place K F',
      w.restrict F ∉ S → w.ramificationIndex F = 1 := by
  classical
  obtain ⟨T, hT⟩ :=
    exists_finset_forall_not_mem_ramificationIndex_eq_one_of_isSeparable
      (K := K) (F := F) (F' := F')
  refine ⟨T.image (fun w : Place K F' => w.restrict F), fun w hw => hT w ?_⟩
  exact fun hwT => hw (Finset.mem_image_of_mem (fun w : Place K F' => w.restrict F) hwT)

end AlgebraicCurve
