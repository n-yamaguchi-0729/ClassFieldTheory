/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeleAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitHerbrandFormula
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits

/-!
# The valuation exact sequence of S-ideles

The actual S-ideles map onto the integer permutation lattice on `S`, with kernel
the everywhere-integral ideles. This is the second exact sequence needed for the
S-unit computation of the idele-class Herbrand quotient.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Actual local orders at the finitely many exceptional places. -/
def sIdeleDivisor (S : Finset (Place k K)) : sIdeles S →* (S → Multiplicative ℤ) where
  toFun a v := localOrder v.val (a.val v.val)
  map_one' := by
    funext v
    exact map_one (localOrder v.val)
  map_mul' a b := by
    funext v
    exact map_mul (localOrder v.val) (a.val v.val) (b.val v.val)

/-- Every integral idele is an S-idele. -/
def integralToSIdeles (S : Finset (Place k K)) :
    integralSubgroup (k := k) (K := K) →* sIdeles S where
  toFun a := ⟨a.val, fun v _ => a.2 v⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem integralToSIdeles_injective (S : Finset (Place k K)) :
    Function.Injective (integralToSIdeles S) :=
  fun _ _ h => Subtype.ext (congrArg (fun a : sIdeles S => (a : IdeleGroup k K)) h)

/-- The valuation map has precisely the everywhere-integral ideles as its kernel. -/
theorem sIdeleDivisor_exact (S : Finset (Place k K)) (a : sIdeles S) :
    sIdeleDivisor S a = 1 ↔ ∃ u, integralToSIdeles S u = a := by
  constructor
  · intro ha
    have hu : a.val ∈ integralSubgroup (k := k) (K := K) := by
      intro v
      by_cases hv : v ∈ S
      · apply (localOrder_eq_zero_iff v (a.val v)).mp
        exact congrArg Multiplicative.toAdd (congrFun ha ⟨v, hv⟩)
      · exact a.2 v hv
    exact ⟨⟨a.val, hu⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    funext v
    apply Multiplicative.ext
    exact (localOrder_eq_zero_iff v.val (u.val v.val)).mpr (u.2 v.val)

/-- Arbitrary integer orders at `S` lift to an actual S-idele. -/
theorem sIdeleDivisor_surjective (S : Finset (Place k K)) :
    Function.Surjective (sIdeleDivisor S) := by
  intro n
  let D := SUnits.ofCoordinates S (fun v => (n v).toAdd)
  obtain ⟨a, ha⟩ := divisor_surjective (k := k) (K := K) (Multiplicative.ofAdd D)
  have hS : a ∈ sIdeles S := by
    intro v hv
    apply (localOrder_eq_zero_iff v (a v)).mp
    rw [← divisor_apply (k := k) (K := K), ha]
    exact SUnits.ofCoordinates_apply_of_not_mem S _ v hv
  refine ⟨⟨a, hS⟩, ?_⟩
  funext v
  apply Multiplicative.ext
  change (localOrder v.val (a v.val)).toAdd = (n v).toAdd
  rw [← divisor_apply (k := k) (K := K), ha]
  exact SUnits.ofCoordinates_apply S _ v

/-- The valuation quotient is exactly the finite integral permutation lattice. -/
def sIdeleQuotientIntegralEquiv (S : Finset (Place k K)) :
    sIdeles S ⧸ (integralToSIdeles S).range ≃* (S → Multiplicative ℤ) := by
  have hker : (integralToSIdeles S).range = (sIdeleDivisor S).ker := by
    ext a
    exact (sIdeleDivisor_exact S a).symm
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sIdeleDivisor S) (sIdeleDivisor_surjective S))

/-- Actual local valuations respect the permutation of places. -/
theorem sIdeleDivisor_smul (S : Finset (Place k K)) (g : SUnits.stabilizer k K S)
    (a : sIdeles S) (v : S) :
    sIdeleDivisor S (g • a) v = sIdeleDivisor S a (g⁻¹ • v) := by
  apply Multiplicative.ext
  change (localOrder v.val ((g.val • a.val) v.val)).toAdd =
    (localOrder (g.val⁻¹ • v.val) (a.val (g.val⁻¹ • v.val))).toAdd
  rw [← divisor_apply (k := k) (K := K), divisor_smul,
    SemilinearAut.divisor_smul_apply, divisor_apply (k := k) (K := K)]

end FunctionField.IdeleGroup
