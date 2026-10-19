/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.HasseNorm

/-!
# The cyclic Hasse norm theorem for function fields

The public statement uses the given function field and a finite cyclic extension.
The extension's function-field presentation and principal divisors are supplied
by the existing finite-extension construction.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- In a finite cyclic function-field extension, a nonzero element is a field
norm exactly when it is a norm at every actual place completion. -/
theorem cyclicHasseNormTheorem (a : Kˣ) :
    (∃ x : L, Algebra.norm K x = (a : K)) ↔
      ∀ w : AlgebraicCurve.Place k L, ∃ x : w.adicCompletion,
        Algebra.norm (w.restrict K).adicCompletion x =
          algebraMap K (w.restrict K).adicCompletion (a : K) := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.NormObstruction.exists_norm_iff_forall_completion_norm
    (k := k) (K := K) (L := L) a

end ClassFieldTheory.FunctionField
