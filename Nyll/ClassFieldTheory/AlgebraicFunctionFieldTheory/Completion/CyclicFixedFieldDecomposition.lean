/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.FieldTheory.Galois.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition

/-!
# The cyclic fixed field of a decomposition automorphism

If an actual automorphism fixes a place, every automorphism over its cyclic
fixed field fixes that same place. The entire Galois group over the fixed
field is therefore the decomposition group. The fixed-field theorem supplies
membership in the original cyclic subgroup; no local-global comparison is
assumed.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K E : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional K E]

/-- Over the cyclic fixed field of a decomposition automorphism, the actual
upper place is fixed by the entire Galois group. -/
theorem decompositionGroup_cyclicFixedField_eq_top (W : Place k E)
    (τ : decompositionGroup (K := K) W) :
    let _ : IsScalarTower k (IntermediateField.fixedField (Subgroup.zpowers τ.1)) E :=
      IsScalarTower.to₁₃₄ k K (IntermediateField.fixedField (Subgroup.zpowers τ.1)) E
    decompositionGroup (K := IntermediateField.fixedField (Subgroup.zpowers τ.1)) W = ⊤ := by
  intro hkFE
  let H : Subgroup Gal(E/K) := Subgroup.zpowers τ.1
  let F : IntermediateField K E := IntermediateField.fixedField H
  have hH : H ≤ decompositionGroup (K := K) W := Subgroup.zpowers_le.mpr τ.2
  apply top_unique
  intro ρ _
  have hρ : ρ.restrictScalars K ∈ F.fixingSubgroup :=
    ((IntermediateField.fixingSubgroupEquiv F).symm ρ).2
  rw [IntermediateField.fixingSubgroup_fixedField] at hρ
  exact hH hρ

end FunctionField.IdeleGroup
