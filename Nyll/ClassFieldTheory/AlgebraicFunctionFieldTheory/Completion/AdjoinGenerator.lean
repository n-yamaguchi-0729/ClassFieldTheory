/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Field generators remain generators after completion

The existing decomposition-group equivalence detects every automorphism of
the completed extension on the image of a global field generator.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A generator of a finite Galois extension generates every corresponding
completed extension over the base completion. -/
theorem completion_adjoin_generator_eq_top
    (w : Place k L) (β : L) (hgen : Algebra.adjoin K {β} = ⊤) :
    Algebra.adjoin (w.restrict K).adicCompletion {algebraMap L w.adicCompletion β} = ⊤ := by
  let b := algebraMap L w.adicCompletion β
  let M := IntermediateField.adjoin (w.restrict K).adicCompletion {b}
  have hfix : M.fixingSubgroup = ⊥ := by
    apply eq_bot_iff.mpr
    intro σ hσ
    have hb : σ b = b := (IntermediateField.mem_fixingSubgroup_iff M σ).mp hσ b
      (IntermediateField.subset_adjoin (w.restrict K).adicCompletion {b} (Set.mem_singleton b))
    obtain ⟨τ, hτ⟩ := (decompositionCompletionEquiv (K := K) w).surjective σ
    have hτone : τ = 1 := by
      apply Subtype.ext
      apply AlgEquiv.coe_toAlgHom_injective
      apply AlgHom.ext_of_adjoin_eq_top hgen
      intro z hz
      have hzβ : z = β := Set.mem_singleton_iff.mp hz
      subst z
      simp only [AlgEquiv.coe_toAlgHom, Subgroup.coe_one, AlgEquiv.one_apply]
      apply (algebraMap L w.adicCompletion).injective
      rw [← decompositionCompletionAut_algebraMap w τ]
      exact (congrArg
        (fun f : Gal(w.adicCompletion/(w.restrict K).adicCompletion) => f b) hτ).trans hb
    change σ = 1
    rw [← hτ, hτone, map_one]
  have hM : M = ⊤ := by
    rw [← IsGalois.fixedField_fixingSubgroup M, hfix, IntermediateField.fixedField_bot]
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (R := (w.restrict K).adicCompletion) b)]
  exact congrArg IntermediateField.toSubalgebra hM

end FunctionField.IdeleGroup
