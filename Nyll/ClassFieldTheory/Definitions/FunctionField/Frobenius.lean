/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.UnramifiedFrobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Arithmetic Frobenius at an unramified function-field place

This is an actual automorphism in the decomposition subgroup. The base
function field and finite extension supply the upper presentation and all
principal-divisor hypotheses used by its construction.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The unique decomposition automorphism inducing arithmetic Frobenius
on the residue field at an unramified place. -/
def arithmeticFrobenius (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1) :
    _root_.FunctionField.IdeleGroup.decompositionGroup (K := K) w := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.unramifiedDecompositionFrobenius (K := K) w he

end ClassFieldTheory.FunctionField
