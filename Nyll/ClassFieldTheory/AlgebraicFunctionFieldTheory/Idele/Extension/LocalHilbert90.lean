/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange

/-!
# Integral correction of local Hilbert 90 primitives

At a place of ramification index one, an element of the base completion has any
prescribed normalized order in the extension completion. Dividing a local
Hilbert 90 primitive by such an element makes it an integral unit and preserves
all coboundaries for automorphisms over the base completion. This applies in
every residue characteristic.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open AlgebraicCurve

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- An automorphism over the base completion fixes each actual included local unit. -/
theorem localAlgAut_smul_localBaseChange (w : Place k L)
    (τ : w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion)
    (x : (w.restrict K).adicCompletionˣ) :
    τ • localBaseChange (K := K) w x = localBaseChange (K := K) w x := by
  apply Units.ext
  exact τ.commutes (x : (w.restrict K).adicCompletion)

/-- At ramification index one, base completion elements realize every upstairs order. -/
theorem exists_localBaseChange_localOrder_eq_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1) (x : w.adicCompletionˣ) :
    ∃ z : (w.restrict K).adicCompletionˣ,
      localOrder w (localBaseChange (K := K) w z) = localOrder w x := by
  let z : (w.restrict K).adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K)
      (localOrder w x).toAdd
  refine ⟨z, ?_⟩
  apply Multiplicative.ext
  change (localOrder w (Units.map
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion) z)).toAdd = _
  rw [localOrder_completionMap, he]
  simpa only [Nat.cast_one, one_mul] using
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K)
      (localOrder w x).toAdd

/-- A local primitive can be made integral without changing any of its base-linear
coboundaries at an unramified place. The same correcting factor works for all automorphisms. -/
theorem exists_localUnit_coboundaries_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1) (x : w.adicCompletionˣ) :
    ∃ y : w.adicCompletionˣ, y ∈ w.adicCompletionIntegers.units ∧
      ∀ τ : w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion,
        (τ • y) / y = (τ • x) / x := by
  obtain ⟨z, hz⟩ := exists_localBaseChange_localOrder_eq_of_ramificationIndex_eq_one w he x
  refine ⟨x / localBaseChange (K := K) w z, ?_, ?_⟩
  · apply (localOrder_eq_zero_iff w _).mp
    rw [map_div, hz, toAdd_div, sub_self]
  · intro τ
    rw [smul_div', localAlgAut_smul_localBaseChange]
    exact div_div_div_cancel_right _ _ _

/-- In particular a primitive for one cyclic local coboundary can be chosen integral. -/
theorem exists_localUnit_coboundary_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (τ : w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion)
    (x : w.adicCompletionˣ) :
    ∃ y : w.adicCompletionˣ, y ∈ w.adicCompletionIntegers.units ∧
      (τ • y) / y = (τ • x) / x := by
  obtain ⟨y, hy, hc⟩ := exists_localUnit_coboundaries_of_ramificationIndex_eq_one w he x
  exact ⟨y, hy, hc τ⟩

end FunctionField.IdeleGroup
