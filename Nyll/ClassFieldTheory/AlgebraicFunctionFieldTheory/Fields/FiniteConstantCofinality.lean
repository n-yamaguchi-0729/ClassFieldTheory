/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure

/-!
# Actual finite constant subfields occur in the degree tower

Inside the original separably closed field, a finite extension of the
finite base is the selected subfield of its actual degree. The comparison
is equality of subfields, so their inclusion maps and scalar structures
are retained when finite cover models are reindexed by degree.
-/

noncomputable section

namespace FunctionField

/-- A finite constant subfield is the original degree stage with the same
degree, as an actual subfield of the given ambient field. -/
theorem finiteIntermediateField_eq_finiteConstantsInClosure
    (k Ω : Type*) [Field k] [Finite k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (E : IntermediateField k Ω) [FiniteDimensional k E]
    (n : ℕ) [NeZero n] (hn : Module.finrank k E = n) :
    E = (finiteConstantsInClosure k Ω n).toIntermediateField := by
  have hEfinite : Finite E := Module.finite_of_finite k
  let D := finiteConstantsInClosure k Ω n
  have hDfinite : Finite D := finite_finiteConstantsInClosure k Ω n
  have hdegree : Module.finrank k E = Module.finrank k D :=
    hn.trans (finrank_finiteConstantsInClosure k Ω n).symm
  apply le_antisymm
  · have hd : Module.finrank k E ∣ Module.finrank k D := by rw [hdegree]
    obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
    let j : E →ₐ[k] Ω := D.toIntermediateField.val.comp f
    have hj : j.fieldRange = E := AlgHom.fieldRange_of_normal j
    intro x hx
    rw [← hj] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact (f y).2
  · have hd : Module.finrank k D ∣ Module.finrank k E := by rw [hdegree]
    obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
    let j : D →ₐ[k] Ω := E.val.comp f
    have hj : j.fieldRange = D.toIntermediateField := AlgHom.fieldRange_of_normal j
    intro x hx
    rw [← hj] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact (f y).2

end FunctionField
