/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteNormProperties
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology

/-!
# Continuous norm and inclusion for arbitrary finite function-field extensions

The upper function-field presentation and principal divisors are supplied
from the original finite extension. The maps are the existing all-place norm
and inclusion descended to the usual idele class groups, including inseparable
extensions.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L]

/-- The continuous idele-class norm of any finite extension of function fields. -/
def ideleClassNorm :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup k L →ₜ* _root_.FunctionField.IdeleClassGroup k K := by
  intro hK hL
  exact _root_.FunctionField.IdeleClassGroup.finiteNormContinuous (k := k) (K := K) (L := L)

/-- The continuous inclusion of idele classes for any finite extension.
The principal-divisor structures are supplied by the given function field. -/
def ideleClassInclusion :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup k K →ₜ* _root_.FunctionField.IdeleClassGroup k L := by
  intro hK hL
  exact
    { toMonoidHom := _root_.FunctionField.IdeleClassGroup.baseChange
        (k := k) (K := K) (L := L)
      continuous_toFun := _root_.FunctionField.IdeleClassGroup.continuous_baseChange
        (k := k) (K := K) (L := L) }

end ClassFieldTheory.FunctionField
