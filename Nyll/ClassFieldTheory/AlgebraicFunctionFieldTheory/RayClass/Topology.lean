/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ClassFieldTheory.Algebra.LocalField.PrincipalUnitTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Topology of all-place ray congruence subgroups

Only the finitely many places in the modulus support impose conditions beyond
integral units. This gives compact open congruence subgroups and open ray subgroups
of the actual idele class group.
-/

noncomputable section

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- Higher units are open in every actual place completion. -/
theorem isOpen_localHigherUnitGroup (v : AlgebraicCurve.Place k K) (n : ℕ) :
    IsOpen (localHigherUnitGroup v n : Set v.adicCompletionˣ) := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  exact LocalFieldTheory.isOpen_fieldPrincipalUnits v.adicCompletion n

/-- Congruence at a finitely supported modulus is an open idele condition. -/
theorem isOpen_congruenceSubgroup (m : Modulus k K) :
    IsOpen (congruenceSubgroup m : Set (IdeleGroup k K)) := by
  classical
  let U : Set (IdeleGroup k K) :=
    (IdeleGroup.integralSubgroup (k := k) (K := K) : Set (IdeleGroup k K)) ∩
      ⋂ v ∈ m.support, (fun a : IdeleGroup k K => a v) ⁻¹'
        (localHigherUnitGroup v (m v) : Set v.adicCompletionˣ)
  have hU : IsOpen U :=
    IdeleGroup.isOpen_integralSubgroup.inter
      (isOpen_biInter_finset fun v _ =>
        (isOpen_localHigherUnitGroup v (m v)).preimage
          (RestrictedProduct.continuous_eval v))
  have hEq : (congruenceSubgroup m : Set (IdeleGroup k K)) = U := by
    ext a
    constructor
    · intro ha
      refine ⟨congruenceSubgroup_le_integralSubgroup m ha, ?_⟩
      exact Set.mem_iInter.mpr fun v => Set.mem_iInter.mpr fun _ => ha v
    · rintro ⟨ha, hS⟩
      intro v
      by_cases hv : v ∈ m.support
      · exact Set.mem_iInter.mp (Set.mem_iInter.mp hS v) hv
      · rw [Finsupp.notMem_support_iff.mp hv, localHigherUnitGroup_zero]
        exact ha v
  rw [hEq]
  exact hU

/-- Congruence subgroups are compact, as closed subgroups of the integral ideles. -/
theorem isCompact_congruenceSubgroup (m : Modulus k K) :
    IsCompact (congruenceSubgroup m : Set (IdeleGroup k K)) :=
  IdeleGroup.isCompact_integralSubgroup.of_isClosed_subset
    ((congruenceSubgroup m).isClosed_of_isOpen (isOpen_congruenceSubgroup m))
    (congruenceSubgroup_le_integralSubgroup m)

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Ray congruence remains open after passage to idele classes. -/
theorem isOpen_rayClassSubgroup (m : Modulus k K) :
    IsOpen (rayClassSubgroup m : Set (IdeleClassGroup k K)) :=
  QuotientGroup.isOpenMap_coe _ (isOpen_congruenceSubgroup m)

/-- The ray subgroup in the idele class group is compact. -/
theorem isCompact_rayClassSubgroup (m : Modulus k K) :
    IsCompact (rayClassSubgroup m : Set (IdeleClassGroup k K)) :=
  (isCompact_congruenceSubgroup m).image QuotientGroup.continuous_mk

end FunctionField.RayClass
