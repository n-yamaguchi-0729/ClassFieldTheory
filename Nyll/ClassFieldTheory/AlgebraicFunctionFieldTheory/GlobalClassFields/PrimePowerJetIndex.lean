/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimePowerJetClassSubgroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.PrimePowerCongruenceIndex

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPrimePowerJets

/-!
# The index of characteristic-power jet classes

Local congruence quotients contribute p for each valuation direction.
The finite diagonal S-unit image cancels all but one of these factors.
The remaining residue-field powers count the local principal-unit layers.
-/

noncomputable section
open AlgebraicCurve
open scoped BigOperators

namespace FunctionField.SUnits

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual finite local jet product has its residue-degree weighted order. -/
theorem card_localPrimePowerJetProduct (m : RayClass.Modulus k K)
    (S : Finset (Place k K)) (hm : ∀ v ∈ S, 1 ≤ m v) :
    Nat.card (localPrimePowerJetProduct p (p • m) S) =
      p ^ S.card * Nat.card k ^ (∑ v : S, (p * m v.val - m v.val) * v.val.deg) := by
  classical
  rw [Nat.card_pi]
  have hprod : (∏ v : S, Nat.card (v.val.adicCompletionˣ ⧸
      ((powMonoidHom (α := v.val.adicCompletionˣ) p).range ⊔
        RayClass.localHigherUnitGroup v.val ((p • m) v.val)))) =
      ∏ v : S, p * Nat.card k ^ ((p * m v.val - m v.val) * v.val.deg) := by
    apply Finset.prod_congr rfl
    intro v _
    exact card_completionPrimePowerCongruenceQuotient p v.val (m v.val) (hm v.val v.property)
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Finset.prod_pow_eq_pow_sum]

end FunctionField.SUnits

namespace FunctionField.IdeleGroup

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- An actual finite depth makes the S-idele jet-class index equal to the
degree count of the bounded Artin–Schreier parameter space. -/
theorem exists_index_primePowerJetClassSubgroup
    (S : Finset (Place k K)) (hSne : S.Nonempty)
    (hS : Function.Surjective (sIdeleClass S)) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ m : RayClass.Modulus k K, (∀ v ∈ S, r ≤ m v) →
      (primePowerJetClassSubgroup p (p • m) S).index =
        p * Nat.card k ^ (∑ v : S, (p * m v.val - m v.val) * v.val.deg) := by
  classical
  obtain ⟨r, hr, hjet⟩ := SUnits.exists_localPrimePowerJetMap_ker_card p S hSne
  refine ⟨r, hr, fun m hm => ?_⟩
  have hdepth : ∀ v ∈ S, r ≤ (p • m) v := by
    intro v hv
    change r ≤ p * m v
    exact (hm v hv).trans (Nat.le_mul_of_pos_left (m v) (Fact.out : p.Prime).pos)
  have hcard := (hjet (p • m) hdepth).2
  let H : Subgroup (SUnits.localPrimePowerJetProduct p (p • m) S) :=
    MonoidHom.range (G := SUnits.units k K S)
      (N := SUnits.localPrimePowerJetProduct p (p • m) S)
      (SUnits.localPrimePowerJetMap p (p • m) S)
  have hmul := H.card_mul_index
  rw [hcard, SUnits.card_localPrimePowerJetProduct p m S
    (fun v hv => hr.trans (hm v hv))] at hmul
  have hScard : 1 ≤ S.card := hSne.card_pos
  have hpS : p ^ S.card = p ^ (S.card - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hScard]
  rw [hpS, mul_assoc] at hmul
  rw [index_primePowerJetClassSubgroup p (p • m) S hS]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos (S.card - 1)) hmul

end FunctionField.IdeleGroup
