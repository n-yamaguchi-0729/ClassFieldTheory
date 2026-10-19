/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.Definitions.FunctionField.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm

/-!
# Norm compatibility of finite function-field reciprocity

Any finite change of base is allowed, including inseparable extensions.
The function-field presentation and principal divisors over the new base are
supplied by its actual finite extension of the original function field.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K F L M : Type) [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k F M] [IsScalarTower k L M]
    [IsScalarTower K F M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K F]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]

/-- Public norm reciprocity for an arbitrary finite base change and a
compatible square of finite abelian extensions. -/
theorem finiteArtin_norm_restrictNormal :
    let presentation := finiteExtensionRatFuncAlgebra k K F
    let _ : Algebra (RatFunc k) F := presentation.val
    have _ : IsScalarTower k (RatFunc k) F := presentation.property.1
    have _ : _root_.FunctionField k F := presentation.property.2
    have _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    have _ : AlgebraicCurve.HasPrincipalDivisors k F :=
      (_root_.FunctionField.isCurveOver k F).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k F,
      AlgEquiv.restrictNormalHom L ((finiteArtin k F M c).restrictScalars K) =
        finiteArtin k K L
          (ideleClassNorm k K F c) := by
  intro presentation aRF hkRF hfunctionF hK hF c
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  have hM : AlgebraicCurve.HasPrincipalDivisors k M :=
    (finiteExtension_isCurveOver k F M).toHasPrincipalDivisors
  exact _root_.FunctionField.abelianFiniteArtin_finiteNorm_restrictNormal
    (K := K) (F := F) (L := L) (M := M) c

end ClassFieldTheory.FunctionField
