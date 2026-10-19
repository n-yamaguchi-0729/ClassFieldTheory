/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois

/-!
# Abelian Galois groups at the actual completions

The completed Galois group is the actual decomposition subgroup. In an
abelian global extension this makes the completed extension abelian as well.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place IsMulCommutative

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Every actual completion of a finite abelian extension is abelian over
the completion at its restricted place. -/
instance completionIsAbelianGalois (w : Place k L) :
    IsAbelianGalois (w.restrict K).adicCompletion w.adicCompletion where
  is_comm.comm σ τ := by
    obtain ⟨σ, rfl⟩ := (decompositionCompletionEquiv (K := K) w).surjective σ
    obtain ⟨τ, rfl⟩ := (decompositionCompletionEquiv (K := K) w).surjective τ
    rw [← map_mul, ← map_mul, mul_comm]

end FunctionField.IdeleGroup
