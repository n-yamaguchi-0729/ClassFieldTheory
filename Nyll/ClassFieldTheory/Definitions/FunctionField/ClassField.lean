/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.Classification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Actual function-field class fields

These definitions reuse the existing finite abelian intermediate fields and
ordinary open subgroups. The classification is the proved actual norm
correspondence, and its inverse selects the unique actual class field.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

/-- Finite abelian intermediate fields of the chosen separable closure,
ordered by field inclusion. The existing field-only definition is reused. -/
abbrev FiniteAbelianExtension (K : Type) [Field K] :=
  ClassFieldTheory.FiniteAbelianLocalExtension K

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- Ordinary open finite-index subgroups of the actual idele-class group. -/
abbrev OpenFiniteIndexSubgroup : Type :=
  let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  {H : OpenSubgroup (_root_.FunctionField.IdeleClassGroup k K) // H.toSubgroup.FiniteIndex}

/-- The actual class norm, with its ordinary openness and finite index. -/
def finiteAbelianNormSubgroup (E : FiniteAbelianExtension K) :
    OpenFiniteIndexSubgroup k K := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.finiteAbelianNormOpenSubgroup k K E

/-- The actual norm correspondence reverses field and subgroup inclusion. -/
def classFieldCorrespondence :
    FiniteAbelianExtension K ≃o (OpenFiniteIndexSubgroup k K)ᵒᵈ := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.finiteAbelianFieldNormSubgroupOrderIso k K

/-- The unique actual class field of an ordinary open finite-index subgroup. -/
def classField (H : OpenFiniteIndexSubgroup k K) : FiniteAbelianExtension K :=
  (classFieldCorrespondence k K).symm (OrderDual.toDual H)

end ClassFieldTheory.FunctionField
