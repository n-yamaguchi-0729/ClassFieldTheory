/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.TopologicalProfiniteCompletion

/-!
# Continuous and profinite function-field reciprocity

The absolute abelian Galois group and the completion over ordinary open
finite quotients are the existing canonical constructions. The Artin map
and the topological group isomorphism use the proved reciprocity maps.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

/-- The actual absolute abelian Galois group with its profinite topology. -/
abbrev AbsoluteAbelianGaloisGroup (K : Type) [Field K] : ProfiniteGrp :=
  LocalClassFieldTheory.localAbsoluteAbelianProfinite K

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- The completion over all finite quotients open for the ordinary
idele-class topology. -/
abbrev IdeleClassProfiniteCompletion : ProfiniteGrp :=
  let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  LocalClassFieldTheory.TopologicalProfiniteCompletion (_root_.FunctionField.IdeleClassGroup k K)

/-- Continuous absolute reciprocity on the actual idele-class group. -/
def absoluteArtin :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup k K →ₜ* AbsoluteAbelianGaloisGroup K := by
  intro hK
  exact _root_.FunctionField.absoluteArtin k K

/-- The canonical continuous map to the ordinary profinite completion. -/
def ideleClassCompletionMap :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup k K →ₜ* IdeleClassProfiniteCompletion k K := by
  intro hK
  exact LocalClassFieldTheory.topologicalProfiniteCompletionMap
    (_root_.FunctionField.IdeleClassGroup k K)

/-- Reciprocity identifies the ordinary profinite completion with the
actual absolute abelian Galois group as topological groups. -/
def profiniteReciprocity :
    IdeleClassProfiniteCompletion k K ≃ₜ* AbsoluteAbelianGaloisGroup K := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.profiniteReciprocity k K

/-- Arithmetic Frobenius degree on the actual absolute abelian Galois group. -/
def absoluteAbelianDegree : AbsoluteAbelianGaloisGroup K →ₜ* ClassFormation.ZHatMul :=
  _root_.FunctionField.absoluteAbelianDegree k K

/-- The independent continuous extension of normalized integer idele degree
through the ordinary profinite completion. -/
def completedNormalizedDegree :
    IdeleClassProfiniteCompletion k K →ₜ* ClassFormation.ZHatMul := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.completedNormalizedDegree k K

end ClassFieldTheory.FunctionField
