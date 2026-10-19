/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom

/-!
# Continuous finite abelian function-field reciprocity

The finite Artin map takes values in the actual relative Galois group.
Its actual norm kernel is open for the usual idele-class topology, proving
continuity for the Krull topology on the Galois group.
-/

noncomputable section

namespace FunctionField

open scoped IsMulCommutative

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The finite abelian Artin homomorphism, using the chosen separable-closure realization. -/
def abelianFiniteArtin : IdeleClassGroup k K →* Gal(L/K) :=
  (Abelianization.equivOfComm (H := Gal(L/K))).symm.toMonoidHom.comp
    (finiteArtin k K L)

/-- Abelianization of the actual automorphism recovers the finite Artin symbol. -/
theorem abelianFiniteArtin_of (c : IdeleClassGroup k K) :
    Abelianization.of (abelianFiniteArtin k K L c) = finiteArtin k K L c :=
  (Abelianization.equivOfComm (H := Gal(L/K))).apply_symm_apply (finiteArtin k K L c)

/-- Finite abelian reciprocity is surjective. -/
theorem abelianFiniteArtin_surjective : Function.Surjective (abelianFiniteArtin k K L) :=
  (Abelianization.equivOfComm (H := Gal(L/K))).symm.surjective.comp
    (finiteArtin_surjective k K L)

/-- Triviality is equivalent to being an actual all-place class norm. -/
theorem abelianFiniteArtin_eq_one_iff_mem_norm (c : IdeleClassGroup k K) :
    abelianFiniteArtin k K L c = 1 ↔
      c ∈ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  change (Abelianization.equivOfComm (H := Gal(L/K))).symm (finiteArtin k K L c) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact finiteArtin_eq_one_iff_mem_norm k K L c

/-- The abelian Artin kernel is the actual norm subgroup. -/
theorem abelianFiniteArtin_ker : (abelianFiniteArtin k K L).ker =
    (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  apply Subgroup.ext
  intro c
  exact abelianFiniteArtin_eq_one_iff_mem_norm k K L c

/-- The actual norm quotient is isomorphic to the actual relative abelian Galois group. -/
def abelianFiniteNormQuotientEquiv :
    (IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
      Gal(L/K) :=
  (finiteNormQuotientEquiv k K L).trans (Abelianization.equivOfComm (H := Gal(L/K))).symm

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- Reciprocity is continuous for the usual idele-class and Krull topologies. -/
theorem continuous_abelianFiniteArtin : Continuous (abelianFiniteArtin k K L) := by
  apply ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete
  rw [abelianFiniteArtin_ker]
  exact IdeleClassGroup.isOpen_norm_range

end FunctionField
