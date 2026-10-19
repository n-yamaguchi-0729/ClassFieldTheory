/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Compact

/-!
# Compact integral units over all places

The actual local integer-unit subgroups are compact. Their unrestricted product embeds
continuously in the idele group with exactly the everywhere-integral ideles as its image.
This proves compactness of the integral subgroup for the restricted-product topology,
as well as local compactness of the full idele group.
-/

open scoped RestrictedProduct Valued WithZero

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace IdeleGroup

/-- Ideles that are integral units at every place, including places above infinity. -/
abbrev integralSubgroup : Subgroup (IdeleGroup k K) :=
  RestrictedProduct.DiscreteValuation.integralSubgroup
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)

@[simp]
theorem mem_integralSubgroup_iff (a : IdeleGroup k K) :
    a ∈ integralSubgroup ↔
      ∀ v : AlgebraicCurve.Place k K, a v ∈ v.adicCompletionIntegers.units :=
  Iff.rfl

/-- Everywhere-integral ideles form an open subgroup for the restricted-product topology. -/
theorem isOpen_integralSubgroup :
    IsOpen (integralSubgroup (k := k) (K := K) : Set (IdeleGroup k K)) :=
  RestrictedProduct.isOpen_forall_mem isOpen_localUnits

end IdeleGroup

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Finite k]

/-- The integral-unit subgroup of the actual completion is compact. -/
theorem isCompact_localUnits (v : AlgebraicCurve.Place k K) :
    IsCompact (v.adicCompletionIntegers.units : Set v.adicCompletionˣ) :=
  Submonoid.units_isCompact (isCompact_localIntegers v)

namespace IdeleGroup

/-- The all-place idele group is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (IdeleGroup k K) := by
  have (v : AlgebraicCurve.Place k K) : LocallyCompactSpace v.adicCompletion :=
    placeCompletion_locallyCompactSpace v
  exact RestrictedProduct.locallyCompactSpace_of_group
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
    (Filter.Eventually.of_forall isCompact_localUnits)

/-- The group of everywhere-integral ideles is compact. -/
theorem isCompact_integralSubgroup :
    IsCompact (integralSubgroup (k := k) (K := K) : Set (IdeleGroup k K)) :=
  RestrictedProduct.isCompact_forall_mem
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers.units)
    Filter.cofinite isCompact_localUnits

/-- The compact-space certificate uses the subgroup topology inherited from the idele group. -/
theorem integralSubgroup_compactSpace :
    CompactSpace (integralSubgroup (k := k) (K := K)) :=
  isCompact_iff_compactSpace.mp isCompact_integralSubgroup

end IdeleGroup

end FunctionField
