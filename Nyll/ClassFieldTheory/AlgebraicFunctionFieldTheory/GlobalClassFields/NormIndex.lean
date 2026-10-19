/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Index
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology

/-!
# The actual norm index of a finite abelian function-field extension

Finite reciprocity identifies the index of the actual idele-class norm
subgroup with the ordinary extension degree.
-/

noncomputable section

namespace FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The norm index of an arbitrary finite abelian function-field extension is its degree. -/
theorem finiteAbelian_norm_index :
    (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range.index = Module.finrank K L := by
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr (abelianFiniteNormQuotientEquiv k K L).toEquiv).trans
    (IsGalois.card_aut_eq_finrank K L)

/-- Pulling a subgroup inside the actual norm image back along the norm
divides its index by the extension degree. -/
theorem finiteAbelian_norm_comap_index_mul_finrank
    (U : Subgroup (IdeleClassGroup k K))
    (hU : U ≤ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) :
    (U.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))).index *
        Module.finrank K L = U.index := by
  rw [Subgroup.index_comap, ← finiteAbelian_norm_index k K L]
  exact Subgroup.relIndex_mul_index hU

/-- Over a nontrivial actual abelian extension, the norm preimage of a
finite-index open subgroup inside its norm image is open and has strictly
smaller index. This supplies the induction measure without assuming a class
field for an arbitrary open subgroup. -/
theorem finiteAbelian_norm_comap_open_index_lt
    (U : Subgroup (IdeleClassGroup k K)) [U.FiniteIndex]
    (hopen : IsOpen (U : Set (IdeleClassGroup k K)))
    (hU : U ≤ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range)
    (hdegree : 1 < Module.finrank K L) :
    IsOpen ((U.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))) :
        Set (IdeleClassGroup k L)) ∧
      (U.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))).index < U.index := by
  refine ⟨hopen.preimage (IdeleClassGroup.continuous_norm (k := k) (K := K) (L := L)), ?_⟩
  have hpositive : 0 <
      (U.comap (IdeleClassGroup.norm (k := k) (K := K) (L := L))).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hlt := Nat.mul_lt_mul_of_pos_left hdegree hpositive
  rw [Nat.mul_one, finiteAbelian_norm_comap_index_mul_finrank k K L U hU] at hlt
  exact hlt

end FunctionField
