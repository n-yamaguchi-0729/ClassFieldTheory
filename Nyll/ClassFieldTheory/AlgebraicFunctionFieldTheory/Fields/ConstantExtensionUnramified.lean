/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGeneration
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
import Nyll.AlgebraicCurves.Places.ConstantExtension.RamificationIndexForgetConstantsEqOneAdjoinRangeEqTop

/-!
# Actual constant extensions are unramified

The constant compositum constructed inside the ambient field satisfies the
existing geometric unramifiedness criterion. Every place extends uniquely when
the same function field is viewed over its larger algebraic constant field.
Consequently adjoining finite constants preserves the order of every element
of the original function field at every place above it.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Finite k] (C : IntermediateField k Ω) [FiniteDimensional k C]

/-- Every place of the actual finite constant compositum has ramification index one. -/
theorem ramificationIndex_constantExtension
    (w : Place k (IntermediateField.adjoin K (C : Set Ω))) :
    w.ramificationIndex K = 1 := by
  let _ : Algebra C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantAlgebra (K := K) C
  have : IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantScalarTower (K := K) C
  have : FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) :=
    finiteDimensional_constantExtension_of_finite (K := K) C
  have h := Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
    (K := k) (K' := C) (F := K)
    (F' := IntermediateField.adjoin K (C : Set Ω))
    (constantExtension_adjoin_constants (K := K) C) (w.extendConstants C)
  have hw : (w.extendConstants C).forgetConstants (K := k) = w := Place.ext rfl
  rw [hw] at h
  exact h

/-- Adjoining finite constants preserves orders of functions from the original field. -/
theorem ord_constantExtension_algebraMap
    (w : Place k (constantExtensionStage (K := K) C)) (x : K) :
    w.ord (algebraMap K (constantExtensionStage (K := K) C) x) =
      (w.restrict K).ord x := by
  have he : w.ramificationIndex K = 1 := ramificationIndex_constantExtension (K := K) C w
  rw [w.ord_restrict, he, Nat.cast_one, one_mul]

section FullConstants

variable (k K Ω)
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [IsSepClosed Ω]

/-- The actual degree-`n` extension of the full constants is unramified everywhere,
even when the originally specified finite constant field is smaller. -/
theorem ramificationIndex_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (w : Place k (fullConstantDegreeStage k K Ω n)) :
    w.ramificationIndex K = 1 := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact ramificationIndex_constantExtension (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField
    (w.extendConstants (algebraicClosure k K))

/-- Orders in each actual degree-`n` constant extension agree with the orders below. -/
theorem ord_fullConstantDegreeStage_algebraMap (n : ℕ) [NeZero n]
    (w : Place k (fullConstantDegreeStage k K Ω n)) (x : K) :
    w.ord (algebraMap K (fullConstantDegreeStage k K Ω n) x) =
      (w.restrict K).ord x := by
  rw [w.ord_restrict, ramificationIndex_fullConstantDegreeStage k K Ω n w,
    Nat.cast_one, one_mul]

end FullConstants

end FunctionField
