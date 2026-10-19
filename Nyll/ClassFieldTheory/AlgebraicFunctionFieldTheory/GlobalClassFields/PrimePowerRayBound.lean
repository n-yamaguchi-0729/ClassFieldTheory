/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimePowerJetIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierRiemannRoch
import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeles

/-!
# A common bound for ray p-quotients and Artin–Schreier parameters

The finite S-idele presentation, finite-depth p-class detection, and actual
Riemann–Roch bound are enlarged together. Thus a prescribed modulus admits
a larger modulus for which both independent cardinality computations agree.
-/

noncomputable section
open AlgebraicCurve
open scoped BigOperators

namespace FunctionField

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The divisor degree difference is the weighted count of the local p-unit layers. -/
theorem degree_prime_mul_sub_toDivisor (p : ℕ) (hp : 1 ≤ p)
    (m : RayClass.Modulus k K) (S : Finset (Place k K)) (hm : m.support ⊆ S) :
    (Divisor.degree (p • (AlgebraicCurve.Modulus.toDivisor m)) -
      Divisor.degree (AlgebraicCurve.Modulus.toDivisor m)).toNat =
      ∑ v : S, (p * m v.val - m v.val) * v.val.deg := by
  classical
  have hsupp : (AlgebraicCurve.Modulus.toDivisor m).support ⊆ S :=
    Finsupp.support_mapRange.trans hm
  have hdegree : Divisor.degree (AlgebraicCurve.Modulus.toDivisor m) =
      ∑ v : S, (m v.val : ℤ) * v.val.deg := by
    rw [Divisor.degree_eq_sum]
    calc
      _ = ∑ v ∈ S, (AlgebraicCurve.Modulus.toDivisor m) v * (v.deg : ℤ) := by
        apply Finset.sum_subset hsupp
        intro v _ hv
        rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
      _ = _ := (Finset.sum_coe_sort S
        (fun v : Place k K => (AlgebraicCurve.Modulus.toDivisor m) v * (v.deg : ℤ))).symm
  have hmul (v : Place k K) : m v ≤ p * m v :=
    Nat.le_mul_of_pos_left (m v) hp
  have heq : ((∑ v : S, (p * m v.val - m v.val) * v.val.deg : ℕ) : ℤ) =
      Divisor.degree (p • (AlgebraicCurve.Modulus.toDivisor m)) -
        Divisor.degree (AlgebraicCurve.Modulus.toDivisor m) := by
    rw [Nat.cast_sum, map_nsmul, nsmul_eq_mul, hdegree, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.cast_mul, Nat.cast_sub (hmul v.val), Nat.cast_mul]
    ring
  exact (congrArg Int.toNat heq).symm

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- Beyond any prescribed modulus, actual p-jet class indices agree with
the actual bounded AS parameter count at a common effective divisor. -/
theorem exists_primePowerRay_bound (p : ℕ) [Fact p.Prime] [CharP K p]
    (m₀ : RayClass.Modulus k K) :
    ∃ (m : RayClass.Modulus k K) (S : Finset (Place k K)),
      m₀ ≤ m ∧ S.Nonempty ∧ Function.Surjective (IdeleGroup.sIdeleClass S) ∧
      m.support ⊆ S ∧
      (IdeleGroup.primePowerJetClassSubgroup p (p • m) S).index =
        Nat.card (boundedArtinSchreierClasses p (p • (AlgebraicCurve.Modulus.toDivisor m))) := by
  classical
  obtain ⟨D₀, _, hcount⟩ := exists_bound_card_boundedArtinSchreierClasses k K p
  obtain ⟨S₀, hS₀⟩ := IdeleGroup.exists_finset_sIdeleClass_surjective k K
  obtain ⟨v₀⟩ := nonempty_place k K
  let S : Finset (Place k K) := insert v₀ (S₀ ∪ m₀.support ∪ D₀.support)
  have hS₀S : S₀ ⊆ S := fun v hv =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_left _ hv))
  have hm₀S : m₀.support ⊆ S := fun v hv =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_right _ hv))
  have hD₀S : D₀.support ⊆ S := fun v hv =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ hv)
  have hSne : S.Nonempty := ⟨v₀, Finset.mem_insert_self _ _⟩
  have hS : Function.Surjective (IdeleGroup.sIdeleClass S) := by
    intro c
    obtain ⟨a, ha⟩ := hS₀ c
    exact ⟨⟨a.val, IdeleGroup.sIdeles_mono hS₀S a.property⟩, ha⟩
  obtain ⟨r, hr, hindex⟩ := IdeleGroup.exists_index_primePowerJetClassSubgroup p S hSne hS
  let exponent : Place k K → ℕ := fun v =>
    if v ∈ S then r + m₀ v + (D₀ v).toNat else 0
  have hexponent : ∀ v, exponent v ≠ 0 → v ∈ S := by
    intro v hv
    by_contra hn
    exact hv (ite_eq_right hn)
  let m : RayClass.Modulus k K := Finsupp.onFinset S exponent hexponent
  have hmin (v : Place k K) (hv : v ∈ S) :
      m v = r + m₀ v + (D₀ v).toNat := ite_eq_left hv
  have hmout (v : Place k K) (hv : v ∉ S) : m v = 0 := ite_eq_right hv
  have hm : m₀ ≤ m := by
    intro v
    by_cases hv : v ∈ S
    · rw [hmin v hv]
      omega
    · have hm₀ : m₀ v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hm₀S h))
      rw [hmout v hv, hm₀]
  have hdepth : ∀ v ∈ S, r ≤ m v := by
    intro v hv
    rw [hmin v hv]
    omega
  have hD : D₀ ≤ (AlgebraicCurve.Modulus.toDivisor m) := by
    intro v
    change D₀ v ≤ (m v : ℤ)
    by_cases hv : v ∈ S
    · rw [hmin v hv]
      have hn := (D₀ v).self_le_toNat
      omega
    · have hDzero : D₀ v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hD₀S h))
      rw [hmout v hv, hDzero, Nat.cast_zero]
  have hsupp : m.support ⊆ S := Finsupp.support_onFinset_subset
  refine ⟨m, S, hm, hSne, hS, hsupp, ?_⟩
  rw [hindex m hdepth, hcount (AlgebraicCurve.Modulus.toDivisor m) hD,
    degree_prime_mul_sub_toDivisor p (Fact.out : p.Prime).one_lt.le m S hsupp]

end FunctionField
