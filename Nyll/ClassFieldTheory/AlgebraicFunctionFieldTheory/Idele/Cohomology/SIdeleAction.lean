/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeles
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv

/-!
# The equivariant S-idele presentation

The actual stabilizer of the finite place set acts on its S-ideles. The diagonal
S-unit map and the map to idele classes respect the established semilinear actions.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem smul_mem_sIdeles (S : Finset (Place k K))
    (g : SUnits.stabilizer k K S) (a : sIdeles S) : g.val • a.val ∈ sIdeles S := by
  apply (mem_sIdeles_iff S _).mpr
  intro v hv
  have hnonzero := Finsupp.mem_support_iff.mp hv
  rw [divisor_smul, SemilinearAut.divisor_smul_apply] at hnonzero
  have hmem := (mem_sIdeles_iff S a.val).mp a.2 (Finsupp.mem_support_iff.mpr hnonzero)
  have h := (g.2 (g.val⁻¹ • v)).mpr hmem
  rwa [smul_inv_smul] at h

/-- The actual semilinear action restricted to S-ideles. -/
instance sIdelesMulDistribMulAction (S : Finset (Place k K)) :
    MulDistribMulAction (SUnits.stabilizer k K S) (sIdeles S) where
  smul g a := ⟨g.val • a.val, smul_mem_sIdeles S g a⟩
  one_smul a := Subtype.ext (one_smul _ a.val)
  mul_smul g h a := Subtype.ext (mul_smul g.val h.val a.val)
  smul_one g := Subtype.ext (smul_one g.val)
  smul_mul g a b := Subtype.ext (smul_mul' g.val a.val b.val)

variable [HasPrincipalDivisors k K]

/-- The S-unit diagonal is equivariant for the actual stabilizer action. -/
theorem sUnitDiagonal_smul (S : Finset (Place k K))
    (g : SUnits.stabilizer k K S) (x : SUnits.units k K S) :
    sUnitDiagonal S (g • x) = g • sUnitDiagonal S x := by
  apply Subtype.ext
  exact (smul_principalIdele g.val x.val).symm

/-- The S-idele presentation is equivariant for the actual semilinear class action. -/
theorem sIdeleClass_smul (S : Finset (Place k K))
    (g : SUnits.stabilizer k K S) (a : sIdeles S) :
    sIdeleClass S (g • a) = g.val • sIdeleClass S a :=
  (IdeleClassGroup.smul_mk g.val a.val).symm

variable [PerfectField k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The S-unit diagonal is injective because evaluation at any actual place is injective. -/
theorem sUnitDiagonal_injective (S : Finset (Place k K)) :
    Function.Injective (sUnitDiagonal S) := by
  intro x y h
  apply Subtype.ext
  apply principalIdele_injective k K
  exact congrArg Subtype.val h

/-- A surjective S-idele presentation identifies the quotient by actual diagonal S-units. -/
def sIdeleQuotientEquiv (S : Finset (Place k K))
    (hS : Function.Surjective (sIdeleClass S)) :
    sIdeles S ⧸ (sUnitDiagonal S).range ≃* IdeleClassGroup k K := by
  rw [range_sUnitDiagonal]
  exact QuotientGroup.quotientKerEquivOfSurjective (sIdeleClass S) hS

end FunctionField.IdeleGroup
