/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Lifting a cyclic fixed field into the common ambient field

The inclusion of the lifted fixed field has the same image in the upper
field as the original fixed field. Consequently adjoining the same actual
generators still generates the extension, and its defining automorphism
fixes the lifted scalars.
-/

noncomputable section

namespace FunctionField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]

/-- The concrete lift of the cyclic fixed field is a base on which the
same actual automorphism fixes scalars and the same generators generate. -/
theorem cyclicFixedField_lift_adjoin_eq_top_and_fixed
    (τ : Gal(E/K)) (s : Set E)
    (hgen : IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ))
      s = ⊤) :
    let F := IntermediateField.fixedField (Subgroup.zpowers τ)
    let R := IntermediateField.lift F
    let _ : Algebra R E :=
      (IntermediateField.inclusion (IntermediateField.lift_le F)).toRingHom.toAlgebra
    Algebra.adjoin R s = ⊤ ∧
      ∀ r : R, τ (algebraMap R E r) = algebraMap R E r := by
  intro F R aRE
  have hFEfinite : FiniteDimensional F E := FiniteDimensional.right K F E
  have hrange : Set.range (algebraMap F E) = Set.range (algebraMap R E) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨IntermediateField.liftAlgEquiv F a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(IntermediateField.liftAlgEquiv F).symm a, rfl⟩
  constructor
  · apply top_unique
    intro x _
    have hx : x ∈ Algebra.adjoin F s := by
      rw [IntermediateField.adjoin_eq_top_iff.mp hgen]
      exact trivial
    apply Algebra.mem_adjoin_iff.mpr
    rw [← hrange]
    exact Algebra.mem_adjoin_iff.mp hx
  · intro r
    have hr : algebraMap R E r ∈ F :=
      (IntermediateField.mem_lift (algebraMap R E r)).mp r.2
    exact (IntermediateField.mem_fixedField_iff (Subgroup.zpowers τ) _).mp hr
      τ (Subgroup.mem_zpowers τ)

end FunctionField
