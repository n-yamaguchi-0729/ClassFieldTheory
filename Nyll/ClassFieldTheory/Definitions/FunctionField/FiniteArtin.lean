/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Continuous finite Artin reciprocity for function fields

The public Artin map uses the existing all-place idele class group and its
usual quotient topology. Its continuity is supplied by the proved openness
of the actual norm subgroup. The underlying map is the existing finite
abelian reciprocity construction; no separate idele model is introduced.
The rational parameter of the base field induces the finite extension's
function-field presentation. Its curve theorem supplies principal divisors.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L]

variable [IsAbelianGalois K L]

/-- Finite abelian Artin reciprocity with the usual idele-class and Krull topologies. -/
def finiteArtin :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup k K →ₜ* Gal(L/K) := by
  intro hK
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let _ : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (_root_.FunctionField.isCurveOver k L).toHasPrincipalDivisors
  exact
    { toMonoidHom := _root_.FunctionField.abelianFiniteArtin k K L
      continuous_toFun := _root_.FunctionField.continuous_abelianFiniteArtin k K L }

end ClassFieldTheory.FunctionField
