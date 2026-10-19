/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Finiteness.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# The function-field presentation of a finite extension

The rational parameter of the base field induces the finite extension's
function-field presentation. The existing curve theorem then supplies
principal divisors without an additional presentation as input.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K L : Type*) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L]

/-- The original rational parameter, composed with the given finite extension,
with its proved constant-field compatibility and finite dimension. -/
def finiteExtensionRatFuncAlgebra :
    {a : Algebra (RatFunc k) L //
      let _ : Algebra (RatFunc k) L := a
      IsScalarTower k (RatFunc k) L ∧ _root_.FunctionField k L} := by
  refine ⟨((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra, ?_⟩
  intro aRL
  have hRKL : IsScalarTower (RatFunc k) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRL : IsScalarTower k (RatFunc k) L :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsScalarTower.algebraMap_apply k K L x).trans
        (congrArg (algebraMap K L) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  exact ⟨hkRL, Module.Finite.trans K L⟩

include K in
/-- A finite extension of the given function field satisfies the curve axioms
without requiring a second rational-function-field presentation as input. -/
theorem finiteExtension_isCurveOver : AlgebraicCurve.IsCurveOver k L := by
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let _ : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  exact _root_.FunctionField.isCurveOver k L

end ClassFieldTheory.FunctionField
