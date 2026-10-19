/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.ClassField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Hilbert class fields with prescribed complete splitting

A nonempty finite splitting set makes the everywhere-unramified class field
finite. This is the field selected by the actual ordinary norm correspondence.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- The largest finite abelian extension unramified everywhere and
completely split at the nonempty prescribed finite set of places. -/
def hilbertClassField (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    FiniteAbelianExtension K := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.hilbertClassField k K S hS

end ClassFieldTheory.FunctionField
