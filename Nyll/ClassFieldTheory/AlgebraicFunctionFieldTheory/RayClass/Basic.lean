/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology

/-!
# Ray moduli and congruence subgroups over all places

A modulus is an effective finitely supported divisor, including places above infinity.
The local filtration is the existing one from local class field theory. The full ray
class quotient retains its degree direction; no finiteness is asserted here.
-/

open scoped WithZero
noncomputable section

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An effective ray modulus on the complete curve. -/
abbrev Modulus (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  AlgebraicCurve.Place k K →₀ ℕ

/-- Local higher units, using the canonical valuation relation of the actual completion. -/
abbrev localHigherUnitGroup (v : AlgebraicCurve.Place k K) (n : ℕ) :
    Subgroup v.adicCompletionˣ :=
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  LocalFieldTheory.fieldPrincipalUnits v.adicCompletion n

/-- Depth zero imposes precisely the usual integral-unit condition. -/
theorem localHigherUnitGroup_zero (v : AlgebraicCurve.Place k K) :
    localHigherUnitGroup v 0 = v.adicCompletionIntegers.units := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  change (LocalFieldTheory.principalUnits v.adicCompletion 0).map
    (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits v.adicCompletion) = _
  rw [LocalFieldTheory.principalUnits_zero, Subgroup.map_top]
  apply Subgroup.ext
  intro x
  change x ∈ LocalFieldTheory.localBaseUnitSubgroup v.adicCompletion ↔ _
  have hunit : x ∈ v.adicCompletionIntegers.units ↔ Valued.v (x : v.adicCompletion) = 1 :=
    RestrictedProduct.DiscreteValuation.mem_localUnits_iff v.adicCompletion x
  rw [LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one, hunit]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation v.adicCompletion)
    (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)).eq_one_iff_eq_one

/-- Higher modulus exponents impose stronger local conditions. -/
theorem localHigherUnitGroup_antitone (v : AlgebraicCurve.Place k K)
    {m n : ℕ} (hmn : m ≤ n) : localHigherUnitGroup v n ≤ localHigherUnitGroup v m := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  exact Subgroup.map_mono (LocalFieldTheory.principalUnits_antitone v.adicCompletion hmn)

/-- All local higher units are integral units. -/
theorem localHigherUnitGroup_le_localUnits (v : AlgebraicCurve.Place k K) (n : ℕ) :
    localHigherUnitGroup v n ≤ v.adicCompletionIntegers.units := by
  rw [← localHigherUnitGroup_zero v]
  exact localHigherUnitGroup_antitone v (Nat.zero_le n)

/-- The all-place idele congruence subgroup attached to a ray modulus. -/
def congruenceSubgroup (m : Modulus k K) : Subgroup (IdeleGroup k K) where
  carrier := {a | ∀ v, a v ∈ localHigherUnitGroup v (m v)}
  one_mem' v := (localHigherUnitGroup v (m v)).one_mem
  mul_mem' ha hb v := (localHigherUnitGroup v (m v)).mul_mem (ha v) (hb v)
  inv_mem' ha v := (localHigherUnitGroup v (m v)).inv_mem (ha v)

theorem congruenceSubgroup_le_integralSubgroup (m : Modulus k K) :
    congruenceSubgroup m ≤ IdeleGroup.integralSubgroup (k := k) (K := K) :=
  fun _ ha v => localHigherUnitGroup_le_localUnits v (m v) (ha v)

/-- The zero modulus gives everywhere-integral ideles. -/
theorem congruenceSubgroup_zero :
    congruenceSubgroup (0 : Modulus k K) =
      IdeleGroup.integralSubgroup (k := k) (K := K) := by
  apply Subgroup.ext
  intro a
  change (∀ v, a v ∈ localHigherUnitGroup v 0) ↔
    (∀ v, a v ∈ v.adicCompletionIntegers.units)
  simp only [localHigherUnitGroup_zero]

/-- Modulus divisibility reverses containment of congruence subgroups. -/
theorem congruenceSubgroup_antitone {m n : Modulus k K} (hmn : m ≤ n) :
    congruenceSubgroup n ≤ congruenceSubgroup m :=
  fun _ ha v => localHigherUnitGroup_antitone v (hmn v) (ha v)

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The image of a ray congruence subgroup in the actual idele class group. -/
def rayClassSubgroup (m : Modulus k K) : Subgroup (IdeleClassGroup k K) :=
  (congruenceSubgroup m).map (IdeleClassGroup.mk (k := k) (K := K))

/-- Ray subgroups are normal in the commutative idele class group. -/
instance rayClassSubgroup_normal (m : Modulus k K) : (rayClassSubgroup m).Normal where
  conj_mem a ha g := by
    simpa only [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one] using ha

/-- The full ray class group; its degree part has not been quotiented out. -/
abbrev RayClassGroup (m : Modulus k K) :=
  IdeleClassGroup k K ⧸ rayClassSubgroup m

theorem rayClassSubgroup_antitone {m n : Modulus k K} (hmn : m ≤ n) :
    rayClassSubgroup n ≤ rayClassSubgroup m :=
  Subgroup.map_mono (congruenceSubgroup_antitone hmn)

end FunctionField.RayClass
