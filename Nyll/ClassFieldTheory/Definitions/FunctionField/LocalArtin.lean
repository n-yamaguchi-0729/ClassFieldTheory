/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Continuous local Artin symbols for function fields

The public local map takes values in the actual global Galois group. It uses
the original place completion, and its arithmetic normalization sends a
uniformizer to arithmetic Frobenius in an unramified extension.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Continuous local reciprocity in the global Galois group, in the arithmetic convention. -/
def localArtin (w : AlgebraicCurve.Place k L) :
    (w.restrict K).adicCompletionˣ →ₜ* Gal(L/K) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact
    { toMonoidHom := _root_.FunctionField.localArtin (K := K) w
      continuous_toFun := continuous_subtype_val.comp
        (_root_.FunctionField.localDecompositionArtin (K := K) w).continuous }

end ClassFieldTheory.FunctionField
