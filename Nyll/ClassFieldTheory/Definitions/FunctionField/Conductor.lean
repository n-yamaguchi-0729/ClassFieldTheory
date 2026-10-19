/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.RayClass
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ExtensionConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor

/-!
# Actual global and local conductors

The global effective divisor is the least ray modulus contained in the
actual class norm. The local exponent is the existing conductor of the
actual completed extension. All ancillary function-field structures are
supplied internally.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The least effective modulus whose ray congruences are actual global norms. -/
def extensionConductor : RayClassModulus k K := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.RayClass.extensionConductor (k := k) (K := K) (L := L)

/-- The least higher-unit depth consisting of norms from the completed extension. -/
def localConductorExponent (w : AlgebraicCurve.Place k L) : ℕ := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  let hrelation : ValuativeRel (w.restrict K).adicCompletion :=
    _root_.FunctionField.placeCompletionValuativeRel (w.restrict K)
  have hlocal : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    _root_.FunctionField.placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  exact LocalClassFieldTheory.localConductorExponent
    (w.restrict K).adicCompletion w.adicCompletion

end ClassFieldTheory.FunctionField
