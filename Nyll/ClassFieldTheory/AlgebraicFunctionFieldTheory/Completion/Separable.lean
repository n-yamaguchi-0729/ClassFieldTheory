/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower

/-!
# Actual completions of finite separable extensions

Separability of a semilocal completed factor gives separability over the
restricted-place completion. Transport along a restriction equality retains
the existing completion map, its finite degree, and its canonical valuation.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- A finite separable function-field extension induces a separable extension
of the actual completions at a place and its restriction. -/
theorem completionIsSeparable [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] (w : Place k L) :
    Algebra.IsSeparable (w.restrict K).adicCompletion w.adicCompletion := by
  exact Place.isSeparable_fiberCompletion (w.restrict K)
    ⟨w, Place.mem_fiber.mpr rfl⟩

/-- Identifying the restricted base place preserves the actual finite
separable completed extension and its existing algebra map. -/
theorem completionFiniteSeparableOver [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (completionMapOver v w hw).toAlgebra
    FiniteDimensional v.adicCompletion w.adicCompletion ∧
      Algebra.IsSeparable v.adicCompletion w.adicCompletion := by
  have hf : FiniteDimensional (w.restrict K).adicCompletion w.adicCompletion := inferInstance
  have hs := completionIsSeparable (K := K) w
  subst v
  exact ⟨hf, hs⟩

/-- The canonical completed valuation extends the base valuation after the
actual restricted place is identified with the specified base place. -/
theorem completionCanonical_hasExtension_over [FiniteDimensional K L]
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (completionMapOver v w hw).toAlgebra
    let _ : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    (ValuativeRel.valuation v.adicCompletion).HasExtension
      (ValuativeRel.valuation w.adicCompletion) := by
  subst v
  exact completionCanonical_hasExtension (K := K) w

end FunctionField.IdeleGroup
