/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Algebraic.Integral
import Nyll.SchemeTheory.RingTheory.FieldExtensions.SeparableConstantsTensor

/-!
# Linear disjointness for actual constant extensions

If the separable constants of `K` already belong to `k`, any separable constant
field in a common overfield is linearly disjoint from `K`. Consequently adjoining
that constant field to `K` preserves its degree over `k`. This uses the existing
tensor-field theorem for separably closed constants and the existing degree
formula for linearly disjoint fields.
-/

open scoped TensorProduct

noncomputable section

namespace FunctionField

/-- The actual relative algebraic closure contains every separable constant of
the ambient field over it. -/
theorem separableConstants_fullConstants (k K : Type*) [Field k] [Field K] [Algebra k K] :
    ∀ y : K, IsSeparable (algebraicClosure k K) y →
      y ∈ (algebraMap (algebraicClosure k K) K).range := by
  intro y hy
  have halg : IsAlgebraic k y := hy.isIntegral.trans_isAlgebraic (R := k)
  exact ⟨⟨y, mem_algebraicClosure_iff.mpr halg⟩, rfl⟩

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (C : IntermediateField k Ω) [Algebra.IsSeparable k C]
    (hsc : ∀ y : K, IsSeparable k y → y ∈ (algebraMap k K).range)

include hsc

/-- A separable constant field in the ambient field is linearly disjoint from
the function field when the base contains all its separable constants. -/
theorem constantExtension_linearDisjoint : C.LinearDisjoint K := by
  have hfield : IsField (K ⊗[k] C) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range k K C hsc
  let iK : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
  have hLD : iK.fieldRange.LinearDisjoint C.val.fieldRange :=
    IntermediateField.LinearDisjoint.of_isField' hfield iK C.val
  rw [IntermediateField.fieldRange_val] at hLD
  have hLD' : C.LinearDisjoint iK.fieldRange := hLD.symm
  rw [IntermediateField.linearDisjoint_iff'] at hLD'
  exact hLD'

/-- Adjoining actual separable constants preserves their vector-space rank. -/
theorem rank_constantExtension :
    Module.rank K (IntermediateField.adjoin K (C : Set Ω)) = Module.rank k C :=
  (constantExtension_linearDisjoint C hsc).adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- The degree of the actual constant compositum over the function field equals
the degree of its constant extension. -/
theorem finrank_constantExtension :
    Module.finrank K (IntermediateField.adjoin K (C : Set Ω)) = Module.finrank k C := by
  exact congrArg Cardinal.toNat (rank_constantExtension C hsc)

/-- Adjoining a finite separable constant field gives a finite field extension. -/
theorem finiteDimensional_constantExtension [FiniteDimensional k C] :
    FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_constantExtension C hsc]
  exact Module.finrank_pos

end FunctionField
