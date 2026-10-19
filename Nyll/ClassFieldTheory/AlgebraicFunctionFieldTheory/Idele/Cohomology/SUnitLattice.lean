/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnits
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The degree exact sequence for the S-unit divisor lattice

Finite integer coordinates on the actual set of places identify the supported
degree-zero divisor lattice with the kernel of the actual weighted degree map.
For nonempty `S`, its degree image is an infinite cyclic subgroup of Z. No
degree-one place or degree-one divisor is assumed.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Turn integer coordinates on `S` into an actual finitely supported divisor. -/
def ofCoordinates (S : Finset (Place k K)) : (S → ℤ) →+ Divisor k K where
  toFun a := ∑ v : S, Finsupp.single (v : Place k K) (a v)
  map_zero' := by
    simp only [Pi.zero_apply, Finsupp.single_zero, Finset.sum_const_zero]
  map_add' a b := by
    simp only [Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]

/-- The constructed divisor has exactly the prescribed coordinate at every place of `S`. -/
theorem ofCoordinates_apply (S : Finset (Place k K)) (a : S → ℤ) (v : S) :
    ofCoordinates S a v = a v := by
  classical
  change (∑ w : S, Finsupp.single (w : Place k K) (a w)) v = a v
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single v]
  · exact Finsupp.single_eq_same
  · intro w _ hw
    exact Finsupp.single_eq_of_ne (fun h => hw (Subtype.ext h.symm))
  · exact fun h => (h (Finset.mem_univ v)).elim

/-- The coordinate construction vanishes at every place outside `S`. -/
theorem ofCoordinates_apply_of_not_mem (S : Finset (Place k K)) (a : S → ℤ)
    (v : Place k K) (hv : v ∉ S) : ofCoordinates S a v = 0 := by
  change (∑ w : S, Finsupp.single (w : Place k K) (a w)) v = 0
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro w _
  exact Finsupp.single_eq_of_ne (fun h => hv (h.symm ▸ w.2))

/-- Integer coordinates recover every divisor in the supported degree-zero lattice. -/
theorem ofCoordinates_coordinates (S : Finset (Place k K)) (D : divisorLattice k K S) :
    ofCoordinates S (coordinates S D) = (D : Divisor k K) := by
  apply Finsupp.ext
  intro v
  by_cases hv : v ∈ S
  · exact ofCoordinates_apply S (coordinates S D) ⟨v, hv⟩
  · exact (ofCoordinates_apply_of_not_mem S _ v hv).trans (D.2.2 v hv).symm

/-- The degree homomorphism on the finite place permutation lattice. -/
def weightedDegree (S : Finset (Place k K)) : (S → ℤ) →+ ℤ :=
  Divisor.degree.comp (ofCoordinates S)

/-- Degree uses the actual residue-field degrees as its integer weights. -/
theorem weightedDegree_apply (S : Finset (Place k K)) (a : S → ℤ) :
    weightedDegree S a = ∑ v : S, a v * (v.val.deg : ℤ) := by
  change Divisor.degree (∑ v : S, Finsupp.single v.val (a v)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun v _ => Divisor.degree_single v.val (a v))

/-- The supported degree-zero lattice is the actual kernel of weighted degree. -/
def latticeEquivDegreeKernel (S : Finset (Place k K)) :
    divisorLattice k K S ≃+ (weightedDegree S).ker where
  toFun D := ⟨coordinates S D, by
    change Divisor.degree (ofCoordinates S (coordinates S D)) = 0
    rw [ofCoordinates_coordinates]
    exact D.2.1⟩
  invFun a := ⟨ofCoordinates S a, ⟨a.2, ofCoordinates_apply_of_not_mem S a⟩⟩
  left_inv D := Subtype.ext (ofCoordinates_coordinates S D)
  right_inv a := by
    apply Subtype.ext
    funext v
    exact ofCoordinates_apply S a v
  map_add' D E := Subtype.ext ((coordinates S).map_add D E)

/-- Quotienting the full finite-coordinate lattice by degree zero gives its actual degree image. -/
def degreeQuotientEquivRange (S : Finset (Place k K)) :
    (S → ℤ) ⧸ (weightedDegree S).ker ≃+ (weightedDegree S).range :=
  QuotientAddGroup.quotientKerEquivRange (weightedDegree S)

/-- A coordinate supported at a single actual place has that place's degree. -/
theorem degree_mem_range_weightedDegree (S : Finset (Place k K)) (v : S) :
    (v.val.deg : ℤ) ∈ (weightedDegree S).range := by
  let a : S → ℤ := fun w => (Finsupp.single v.val 1 : Divisor k K) w
  have ha : ofCoordinates S a = (Finsupp.single v.val 1 : Divisor k K) := by
    apply Finsupp.ext
    intro w
    by_cases hw : w ∈ S
    · exact ofCoordinates_apply S a ⟨w, hw⟩
    · rw [ofCoordinates_apply_of_not_mem S a w hw]
      have hwv : w ≠ v.val := fun h => hw (h.symm ▸ v.2)
      exact (Finsupp.single_eq_of_ne hwv).symm
  refine ⟨a, ?_⟩
  change Divisor.degree (ofCoordinates S a) = (v.val.deg : ℤ)
  rw [ha, Divisor.degree_single, one_mul]

/-- A nonempty set of curve places has a nonzero degree image. -/
theorem weightedDegree_range_ne_bot [IsCurveOver k K] (S : Finset (Place k K))
    (hS : S.Nonempty) : (weightedDegree S).range ≠ ⊥ := by
  obtain ⟨v, hv⟩ := hS
  have : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  have hpos : 0 < v.deg := Module.finrank_pos (R := k) (M := v.ResidueField)
  have hmem := degree_mem_range_weightedDegree S ⟨v, hv⟩
  intro hbot
  rw [hbot, AddSubgroup.mem_bot] at hmem
  exact (Nat.cast_ne_zero.mpr hpos.ne') hmem

/-- The actual degree image for nonempty `S` is infinite cyclic, even without a degree-one place. -/
def degreeRangeEquivInt [IsCurveOver k K] (S : Finset (Place k K)) (hS : S.Nonempty) :
    (weightedDegree S).range ≃+ ℤ := by
  have : Infinite (weightedDegree S).range :=
    IsAddCyclic.infinite_of_ne_bot (weightedDegree_range_ne_bot S hS)
  exact intCyclicAddEquiv.symm

end FunctionField.SUnits
