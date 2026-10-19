/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Conductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedNormQuotient

/-!
# The conductor of an actual finite-extension norm subgroup

The proved openness of the actual class norm image supplies its least effective
conductor. Every divisible modulus maps surjectively to the finite norm quotient.
The construction and its tower monotonicity require no reciprocity assumption.
-/

noncomputable section

namespace FunctionField.RayClass

open AlgebraicCurve

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- The least modulus whose ray subgroup consists of actual norms from `L`. -/
def extensionConductor : Modulus k K :=
  conductor (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range
    IdeleClassGroup.isOpen_norm_range

/-- The actual norm subgroup contains the ray subgroup of its conductor. -/
theorem rayClassSubgroup_extensionConductor_le :
    rayClassSubgroup (extensionConductor (k := k) (K := K) (L := L)) ≤
      (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range :=
  rayClassSubgroup_conductor_le _ _

/-- A modulus is divisible by the extension conductor exactly when all its
ray classes are actual norms. -/
theorem extensionConductor_le_iff (m : Modulus k K) :
    extensionConductor (k := k) (K := K) (L := L) ≤ m ↔
      rayClassSubgroup m ≤ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range :=
  conductor_le_iff _ _ m

/-- Every admissible ray quotient maps to the actual finite norm quotient. -/
def rayToNormQuotient (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) :
    IdeleClassGroup k K ⧸ rayClassSubgroup m →*
      IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range :=
  QuotientGroup.map (rayClassSubgroup m)
    (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range
    (MonoidHom.id (IdeleClassGroup k K))
    ((extensionConductor_le_iff (k := k) (K := K) (L := L) m).mp hm)

@[simp]
theorem rayToNormQuotient_mk (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m)
    (c : IdeleClassGroup k K) :
    rayToNormQuotient m hm (QuotientGroup.mk c) = QuotientGroup.mk c := rfl

/-- The actual finite norm quotient is a quotient of every admissible ray group. -/
theorem rayToNormQuotient_surjective (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) :
    Function.Surjective (rayToNormQuotient m hm) := by
  intro q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk c, rfl⟩

section Tower

variable {M : Type} [Field M] [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra.IsSeparable L M] [HasPrincipalDivisors k M]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]

/-- Enlarging a finite Galois extension can only increase its norm conductor. -/
theorem extensionConductor_le_of_tower :
    extensionConductor (k := k) (K := K) (L := L) ≤
      extensionConductor (k := k) (K := K) (L := M) := by
  apply conductor_antitone
  rintro c ⟨b, rfl⟩
  exact ⟨IdeleClassGroup.norm (k := k) (K := L) (L := M) b,
    IdeleClassGroup.norm_trans (k := k) (K := K) (L := L) (M := M) b⟩

end Tower

end FunctionField.RayClass
