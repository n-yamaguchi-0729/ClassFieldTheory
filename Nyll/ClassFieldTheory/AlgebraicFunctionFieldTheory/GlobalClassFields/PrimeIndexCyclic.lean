/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimeIndexClassField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormIndex
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Actual cyclic class fields of prime degree

The norm-index formula computes the degree of the already constructed
prime-index class field. Its Galois group has prime order and is cyclic.
-/

noncomputable section
namespace FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- A prime-index ordinary open subgroup has an actual cyclic class field,
with exactly that subgroup as its norm image. -/
theorem exists_cyclicClassField_of_prime_index
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) (hp : H.index.Prime) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E)
      (_ : IsAbelianGalois K E),
      IsCyclic Gal(E/K) ∧
        (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = H := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  obtain ⟨E, hEfinite, hEabelian, hEnorm⟩ :=
    exists_classField_of_prime_index k K H hH hp
  have hpFact : Fact H.index.Prime := ⟨hp⟩
  have hcard : Nat.card Gal(E/K) = H.index := by
    rw [IsGalois.card_aut_eq_finrank K E, ← finiteAbelian_norm_index k K E, hEnorm]
  exact ⟨E, hEfinite, hEabelian, isCyclic_of_prime_card hcard, hEnorm⟩

end FunctionField
