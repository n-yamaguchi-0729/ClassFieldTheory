/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.Conductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ExtensionConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Conductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Conductor minimality and ramification support

The global conductor has exactly the completed local exponents as its
coefficients. A modulus is admissible exactly when its ray subgroup consists
of actual norms, and every place outside it is unramified.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- A modulus bounds the global conductor exactly when its ray subgroup
is contained in the actual global norm image. -/
theorem extensionConductor_le_iff (m : RayClassModulus k K) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    extensionConductor k K L ≤ m ↔ _root_.FunctionField.RayClass.rayClassSubgroup m ≤
      (_root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  intro hK hL
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  exact _root_.FunctionField.RayClass.extensionConductor_le_iff m

/-- Every coefficient of the global conductor is the actual local conductor
at any place above it. -/
theorem extensionConductor_apply (w : AlgebraicCurve.Place k L) :
    extensionConductor k K L (w.restrict K) = localConductorExponent k K L w := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.RayClass.extensionConductor_apply_eq_localConductor (K := K) w

/-- The completed local conductor vanishes exactly at an unramified place. -/
theorem localConductorExponent_eq_zero_iff (w : AlgebraicCurve.Place k L) :
    localConductorExponent k K L w = 0 ↔ w.ramificationIndex K = 1 := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.localConductorExponent_eq_zero_iff_ramificationIndex_eq_one
    (K := K) w

/-- Every place outside an admissible effective modulus is actually unramified. -/
theorem ramificationIndex_eq_one_of_not_mem_support
    (m : RayClassModulus k K) (hm : extensionConductor k K L ≤ m)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K ∉ m.support) :
    w.ramificationIndex K = 1 := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.RayClass.ramificationIndex_eq_one_of_not_mem_support m hm w hw

end ClassFieldTheory.FunctionField
