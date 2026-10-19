/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantClosure
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation

/-!
# Actual constant extensions in the abstract class formation

Every finite extension of the full constant field is unramified for the
concrete constant-field degree datum. Normality identifies its canonical
separable-closure realization with its given intermediate field.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The actual degree-`n` constant extension is unramified for the actual degree datum. -/
theorem finiteGaloisAbstractExtension_fullConstant_isUnramified (n : ℕ) [NeZero n] :
    (finiteGaloisAbstractExtension K
      (fullConstantDegreeStage k K (SeparableClosure K) n)).IsUnramified
      (fullConstantDegreeData k K (SeparableClosure K)) := by
  let Ω := SeparableClosure K
  let E := fullConstantDegreeStage k K Ω n
  let D := fullConstantDegreeData k K Ω
  let T := finiteGaloisAbstractExtension K E
  have hle : D.inertia.toSubgroup ≤ E.toIntermediateField.fixingSubgroup := by
    rw [fullConstantDegreeData_inertia_eq_iInf]
    exact iInf_le (fun m : ℕ+ =>
      (fullConstantDegreeStage k K Ω (m : ℕ)).toIntermediateField.fixingSubgroup)
        ⟨n, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  apply (T.isUnramified_iff_inertia_le D).2
  intro σ hσ
  have hfix : σ ∈ E.toIntermediateField.fixingSubgroup := hle hσ.2
  let j := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  change σ ∈ j.fieldRange.fixingSubgroup
  rw [ClassFieldTheory.fieldRange_eq_of_normal j E.toIntermediateField.val,
    IntermediateField.fieldRange_val]
  exact hfix

end FunctionField
