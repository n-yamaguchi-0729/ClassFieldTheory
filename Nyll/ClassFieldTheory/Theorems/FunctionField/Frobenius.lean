/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.OrderOfElement
import Nyll.AlgebraicCurves.Places.Ramification.CardFiberOverMulRamificationIndexMulInertiaDeg
import Nyll.ClassFieldTheory.Definitions.FunctionField.Frobenius
import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.Definitions.FunctionField.LocalArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.UnramifiedFrobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor

/-!
# Unramified Frobenius and local norm criteria

The formulas concern the actual local reciprocity map and actual
decomposition group. Equality with the global Artin map on a one-place
idele remains a separate local-global comparison.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Public arithmetic Frobenius raises residues to the base residue cardinality. -/
theorem arithmeticFrobenius_residue (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) (y : w.ResidueField) :
    _root_.FunctionField.IdeleGroup.decompositionResidueAut (K := K) w
      (arithmeticFrobenius k K L w he) y = y ^ Nat.card (w.restrict K).ResidueField := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.unramifiedDecompositionFrobenius_residue w he y

/-- The order of arithmetic Frobenius equals the actual residue degree. -/
theorem orderOf_arithmeticFrobenius (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) :
    orderOf (arithmeticFrobenius k K L w he) = w.inertiaDeg K := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.orderOf_unramifiedDecompositionFrobenius w he

/-- Trivial Frobenius is equivalent to residue degree one at an unramified place. -/
theorem arithmeticFrobenius_eq_one_iff (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) :
    arithmeticFrobenius k K L w he = 1 ↔ w.inertiaDeg K = 1 := by
  rw [← orderOf_eq_one_iff, orderOf_arithmeticFrobenius k K L w he]

/-- Frobenius order measures the number of places above an unramified base place. -/
theorem card_fiberOver_mul_orderOf_arithmeticFrobenius (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) :
    ((w.restrict K).fiberOver L).card * orderOf (arithmeticFrobenius k K L w he) =
      Module.finrank K L := by
  rw [orderOf_arithmeticFrobenius k K L w he]
  have h := AlgebraicCurve.Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
    (w.restrict K) w rfl
  rw [he, one_mul] at h
  exact h

/-- The local Artin value is the local-order power of arithmetic Frobenius. -/
theorem localArtin_eq_arithmeticFrobenius_zpow (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) (x : (w.restrict K).adicCompletionˣ) :
    localArtin k K L w x = (arithmeticFrobenius k K L w he).val ^
      (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact congrArg Subtype.val
    (_root_.FunctionField.localDecompositionArtin_eq_unramifiedFrobenius_zpow w he x)

/-- An unramified local norm is detected by divisibility by the residue degree. -/
theorem exists_localNorm_iff_inertiaDeg_dvd (w : AlgebraicCurve.Place k L)
    (he : w.ramificationIndex K = 1) (x : (w.restrict K).adicCompletionˣ) :
    (∃ y : w.adicCompletionˣ,
      _root_.FunctionField.IdeleGroup.localNorm (K := K) w y = x) ↔
      (w.inertiaDeg K : ℤ) ∣
        (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.mem_localNorm_range_iff_inertiaDeg_dvd w he x

end ClassFieldTheory.FunctionField
