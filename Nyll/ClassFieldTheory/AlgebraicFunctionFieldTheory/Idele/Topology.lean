/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# The restricted-product idele topology

The local integral-unit subgroups are open. Thus Mathlib's restricted-product
instances give the idele group its topological-group structure. Evaluation and
the inclusion of a single local factor are continuous for this topology.
-/

open scoped RestrictedProduct

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Integral units form an open subgroup of the local multiplicative group. -/
theorem isOpen_localUnits (v : AlgebraicCurve.Place k K) :
    IsOpen (v.adicCompletionIntegers.units : Set v.adicCompletionˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

/-- Openness supplies the existing restricted-product topological-group instance. -/
instance localUnitsOpen :
    Fact (∀ v : AlgebraicCurve.Place k K,
      IsOpen (v.adicCompletionIntegers.units : Set v.adicCompletionˣ)) :=
  ⟨isOpen_localUnits⟩

namespace IdeleGroup

/-- Evaluation at a place is a continuous group homomorphism. -/
def componentContinuous (v : AlgebraicCurve.Place k K) :
    IdeleGroup k K →ₜ* v.adicCompletionˣ where
  __ := component v
  continuous_toFun := RestrictedProduct.continuous_eval v

@[simp]
theorem componentContinuous_apply (v : AlgebraicCurve.Place k K) (a : IdeleGroup k K) :
    componentContinuous v a = a v :=
  rfl

/-- Inserting a local multiplicative element at one place is continuous. -/
theorem continuous_placeIdele (v : AlgebraicCurve.Place k K) :
    Continuous (placeIdele v) := by
  classical
  let localLift : v.adicCompletionˣ →
      Πʳ w : AlgebraicCurve.Place k K,
        [w.adicCompletionˣ, w.adicCompletionIntegers.units]_[Filter.principal {v}ᶜ] :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.mpr (by
      intro w hw
      have hne : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne hne]
      exact Subgroup.one_mem _)⟩
  have hlocal : Continuous localLift :=
    RestrictedProduct.continuous_rng_of_principal.mpr
      (continuous_mulSingle (A := fun w : AlgebraicCurve.Place k K => w.adicCompletionˣ) v)
  have hfilter : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (AlgebraicCurve.Place k K)) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  exact (RestrictedProduct.continuous_inclusion hfilter).comp hlocal

/-- The continuous local-to-global inclusion at one place. -/
def placeIdeleContinuous (v : AlgebraicCurve.Place k K) :
    v.adicCompletionˣ →ₜ* IdeleGroup k K where
  __ := placeIdele v
  continuous_toFun := continuous_placeIdele v

@[simp]
theorem placeIdeleContinuous_apply (v : AlgebraicCurve.Place k K)
    (x : v.adicCompletionˣ) : placeIdeleContinuous v x = placeIdele v x :=
  rfl

end IdeleGroup

end FunctionField
