/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitLattice

/-!
# The equivariant degree sequence of the S-unit lattice

The actual stabilizer of `S` permutes its places and acts on integer coordinates
by inverse permutation. The divisor reconstruction intertwines this with the
existing semilinear divisor action. Actual residue degrees are invariant, so
the image of weighted degree has trivial action.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The actual stabilizer permutes the places in `S`. -/
instance placeMulAction (S : Finset (Place k K)) : MulAction (stabilizer k K S) S where
  smul g v := ⟨g.val • v.val, (g.2 v.val).mpr v.2⟩
  one_smul v := Subtype.ext (one_smul _ v.val)
  mul_smul g h v := Subtype.ext (mul_smul g.val h.val v.val)

/-- Integer coordinates carry the inverse-permutation action of the actual stabilizer. -/
instance coordinateDistribMulAction (S : Finset (Place k K)) :
    DistribMulAction (stabilizer k K S) (S → ℤ) where
  smul g a v := a (g⁻¹ • v)
  one_smul a := by
    funext v
    change a ((1 : stabilizer k K S)⁻¹ • v) = a v
    rw [inv_one, one_smul]
  mul_smul g h a := by
    funext v
    change a ((g * h)⁻¹ • v) = a (h⁻¹ • (g⁻¹ • v))
    rw [mul_inv_rev, mul_smul]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- Restricting a divisor to its actual coordinates preserves the stabilizer action. -/
theorem coordinates_smul (S : Finset (Place k K)) (g : stabilizer k K S)
    (D : divisorLattice k K S) : coordinates S (g • D) = g • coordinates S D := by
  funext v
  exact SemilinearAut.divisor_smul_apply g.val D.val v.val

/-- Finite coordinate reconstruction is equivariant for the actual semilinear divisor action. -/
theorem ofCoordinates_smul (S : Finset (Place k K)) (g : stabilizer k K S)
    (a : S → ℤ) : ofCoordinates S (g • a) = g.val • ofCoordinates S a := by
  apply Finsupp.ext
  intro v
  rw [SemilinearAut.divisor_smul_apply]
  by_cases hv : v ∈ S
  · calc
      ofCoordinates S (g • a) v = a (g⁻¹ • (⟨v, hv⟩ : S)) :=
        ofCoordinates_apply S (g • a) ⟨v, hv⟩
      _ = ofCoordinates S a (g.val⁻¹ • v) :=
        (ofCoordinates_apply S a (g⁻¹ • (⟨v, hv⟩ : S))).symm
  · have hv' : g.val⁻¹ • v ∉ S := by
      intro h
      have h' := (g.2 (g.val⁻¹ • v)).mpr h
      rw [smul_inv_smul] at h'
      exact hv h'
    rw [ofCoordinates_apply_of_not_mem S (g • a) v hv,
      ofCoordinates_apply_of_not_mem S a (g.val⁻¹ • v) hv']

/-- Actual weighted degree is unchanged by permutation of places by a semilinear automorphism. -/
theorem weightedDegree_smul (S : Finset (Place k K)) (g : stabilizer k K S)
    (a : S → ℤ) : weightedDegree S (g • a) = weightedDegree S a := by
  change Divisor.degree (ofCoordinates S (g • a)) = Divisor.degree (ofCoordinates S a)
  rw [ofCoordinates_smul, SemilinearAut.degree_smul]

/-- The kernel of weighted degree carries the restricted permutation action. -/
instance degreeKernelDistribMulAction (S : Finset (Place k K)) :
    DistribMulAction (stabilizer k K S) (weightedDegree S).ker where
  smul g a := ⟨g • a.val, (weightedDegree_smul S g a.val).trans a.2⟩
  one_smul a := Subtype.ext (one_smul _ a.val)
  mul_smul g h a := Subtype.ext (mul_smul g h a.val)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g a.val b.val)

/-- The concrete comparison with the weighted-degree kernel is equivariant. -/
theorem latticeEquivDegreeKernel_smul (S : Finset (Place k K))
    (g : stabilizer k K S) (D : divisorLattice k K S) :
    latticeEquivDegreeKernel S (g • D) = g • latticeEquivDegreeKernel S D :=
  Subtype.ext (coordinates_smul S g D)

/-- Semilinear automorphisms act trivially on the actual degree image. -/
instance degreeRangeDistribMulAction (S : Finset (Place k K)) :
    DistribMulAction (stabilizer k K S) (weightedDegree S).range where
  smul _ n := n
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- Weighted degree onto its actual image is equivariant for the trivial image action. -/
theorem weightedDegree_rangeRestrict_smul (S : Finset (Place k K))
    (g : stabilizer k K S) (a : S → ℤ) :
    (weightedDegree S).rangeRestrict (g • a) = g • (weightedDegree S).rangeRestrict a :=
  Subtype.ext (weightedDegree_smul S g a)

/-- The infinite cyclic degree image has the trivial action in its integer coordinate. -/
theorem degreeRangeEquivInt_smul [IsCurveOver k K] (S : Finset (Place k K))
    (hS : S.Nonempty) (g : stabilizer k K S) (n : (weightedDegree S).range) :
    degreeRangeEquivInt S hS (g • n) = degreeRangeEquivInt S hS n := rfl

end FunctionField.SUnits
