/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Compact
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology

/-!
# The all-place adele topology

The integer adeles form a compact open subring. The units carry precisely the
restricted-product idele topology, by the existing common unit equivalence.
-/

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

instance localIntegersOpen :
    Fact (∀ v : AlgebraicCurve.Place k K,
      IsOpen (v.adicCompletionIntegers : Set v.adicCompletion)) :=
  ⟨fun v => Valued.isOpen_valuationSubring v.adicCompletion⟩

namespace AdeleRing

/-- Evaluation is continuous for the restricted-product topology. -/
theorem continuous_component (v : AlgebraicCurve.Place k K) :
    Continuous (component v) :=
  RestrictedProduct.continuous_eval v

/-- The everywhere-integral adeles, including at infinity. -/
def integralSubring : Subring (AdeleRing k K) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers}
  zero_mem' v := v.adicCompletionIntegers.zero_mem
  one_mem' v := v.adicCompletionIntegers.one_mem
  add_mem' ha hb v := v.adicCompletionIntegers.toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := v.adicCompletionIntegers.toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := v.adicCompletionIntegers.toSubring.neg_mem (ha v)

/-- Integral adeles form an open subring. -/
theorem isOpen_integralSubring :
    IsOpen (integralSubring (k := k) (K := K) : Set (AdeleRing k K)) :=
  RestrictedProduct.isOpen_forall_mem fun v : AlgebraicCurve.Place k K =>
    Valued.isOpen_valuationSubring v.adicCompletion

/-- The algebraic unit equivalence also identifies the two topologies. -/
def unitsContinuousMulEquivIdele : (AdeleRing k K)ˣ ≃ₜ* IdeleGroup k K :=
  RestrictedProduct.unitsContinuousMulEquiv
    (B := fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers)
    (fun v => Valued.isOpen_valuationSubring v.adicCompletion)

variable [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The all-place adele ring is locally compact over a finite constant field. -/
theorem locallyCompactSpace : LocallyCompactSpace (AdeleRing k K) := by
  have (v : AlgebraicCurve.Place k K) : LocallyCompactSpace v.adicCompletion :=
    placeCompletion_locallyCompactSpace v
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)
    (Filter.Eventually.of_forall isCompact_localIntegers)

/-- The integer adeles form a compact subring. -/
theorem isCompact_integralSubring :
    IsCompact (integralSubring (k := k) (K := K) : Set (AdeleRing k K)) :=
  RestrictedProduct.isCompact_forall_mem
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers)
    Filter.cofinite isCompact_localIntegers

end AdeleRing

end FunctionField
