/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Nyll.ClassFieldTheory.Definitions.FunctionField.RayClass
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.RayPowerQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SplitRayQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Finite generation and finite quotients of all-place ray class groups

The full ray class group is finitely generated. Its positive power quotients
are finite, and their defining subgroups are open in the ordinary idele-class
topology and cofinal among open finite-index subgroups. These are assertions
about actual idele-class quotients, not an existence theorem for class fields.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- The full all-place ray class group is finitely generated. -/
theorem rayClassGroup_finitelyGenerated (m : RayClassModulus k K) :
    Group.FG (RayClassGroup k K m) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.RayClass.rayClassGroup_fg m

/-- Ray congruences and powers generate an open subgroup for the ordinary topology. -/
theorem isOpen_powerRaySubgroup (m : RayClassModulus k K) (n : ℕ) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    IsOpen (powerRaySubgroup k K m n : Set (_root_.FunctionField.IdeleClassGroup k K)) := by
  intro hK
  exact _root_.FunctionField.RayClass.isOpen_powerRaySubgroup m n

/-- Quotienting actual ray classes by positive powers gives a finite group. -/
theorem finite_powerRayClassGroup (m : RayClassModulus k K) {n : ℕ} (hn : n ≠ 0) :
    Finite (PowerRayClassGroup k K m n) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hindex : (_root_.FunctionField.RayClass.powerRaySubgroup m n).FiniteIndex :=
    _root_.FunctionField.RayClass.finiteIndex_powerRaySubgroup m hn
  exact Subgroup.finite_quotient_of_finiteIndex
    (H := _root_.FunctionField.RayClass.powerRaySubgroup m n)

/-- Every ordinary open finite-index subgroup contains a ray-power subgroup
with positive power equal to its own index. -/
theorem exists_powerRaySubgroup_le :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    ∀ (H : Subgroup (_root_.FunctionField.IdeleClassGroup k K)),
      IsOpen (H : Set (_root_.FunctionField.IdeleClassGroup k K)) →
      H.FiniteIndex →
      ∃ m : RayClassModulus k K, H.index ≠ 0 ∧ powerRaySubgroup k K m H.index ≤ H := by
  intro hK H hH hindex
  exact _root_.FunctionField.RayClass.exists_powerRaySubgroup_le H hH

/-- Prescribed splitting gives an open subgroup in the ordinary topology. -/
theorem isOpen_splitRaySubgroup (m : RayClassModulus k K)
    (S : Finset (AlgebraicCurve.Place k K)) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    IsOpen (splitRaySubgroup k K m S : Set (_root_.FunctionField.IdeleClassGroup k K)) := by
  intro hK
  exact _root_.FunctionField.RayClass.isOpen_splitRaySubgroup m S

/-- A nonempty set of prescribed splitting places gives a finite ray quotient. -/
theorem finite_splitRayClassGroup (m : RayClassModulus k K)
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    Finite (SplitRayClassGroup k K m S) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hindex : (_root_.FunctionField.RayClass.splitRaySubgroup m S).FiniteIndex :=
    _root_.FunctionField.RayClass.finiteIndex_splitRaySubgroup m S hS
  exact Subgroup.finite_quotient_of_finiteIndex
    (H := _root_.FunctionField.RayClass.splitRaySubgroup m S)

end ClassFieldTheory.FunctionField
