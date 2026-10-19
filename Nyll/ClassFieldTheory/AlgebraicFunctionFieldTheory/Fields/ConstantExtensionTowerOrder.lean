/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower

/-!
# The actual constant tower is ordered by divisibility

The finite fields inside the separably closed ambient field form the usual
divisibility tower. Adjoining them to the original function field preserves
these inclusions, and the proved degree formula detects every inclusion.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    {n m : ℕ} [NeZero n] [NeZero m]

/-- Divisibility gives actual containment in the constant extension tower. -/
theorem fullConstantDegreeStage_mono (h : n ∣ m) :
    fullConstantDegreeStage k K Ω n ≤ fullConstantDegreeStage k K Ω m := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact IntermediateField.adjoin.mono K _ _
    (finiteConstantsInClosure_mono (algebraicClosure k K) Ω h)

/-- Inclusions in the actual constant tower are exactly divisibility of degrees. -/
theorem fullConstantDegreeStage_le_iff :
    fullConstantDegreeStage k K Ω n ≤ fullConstantDegreeStage k K Ω m ↔ n ∣ m := by
  constructor
  · intro h
    have hd := IntermediateField.finrank_dvd_of_le_right h
    rw [finrank_fullConstantDegreeStage, finrank_fullConstantDegreeStage] at hd
    exact hd
  · exact fullConstantDegreeStage_mono k K Ω

/-- Positive degrees distinguish the actual fields in the constant tower. -/
theorem fullConstantDegreeStage_eq_iff :
    fullConstantDegreeStage k K Ω n = fullConstantDegreeStage k K Ω m ↔ n = m := by
  constructor
  · intro h
    exact Nat.dvd_antisymm
      ((fullConstantDegreeStage_le_iff k K Ω).mp h.le)
      ((fullConstantDegreeStage_le_iff k K Ω).mp h.ge)
  · rintro rfl
    rfl

end FunctionField
