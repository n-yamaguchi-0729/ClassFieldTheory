/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldDegreeOne

/-!
# Degree-one divisors over the actual full constants

Apply geometric Frobenius descent to the actual relative algebraic closure of
the finite base. The original rational parameter supplies the required finite
function-field presentation over those full constants.
-/

namespace FunctionField

open AlgebraicCurve

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The actual full constant field admits a divisor of degree one on the given function field. -/
theorem exists_fullConstants_divisor_degree_one :
    ∃ D : Divisor (algebraicClosure k K) K, Divisor.degree D = 1 := by
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have hfinite : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hcurve : IsCurveOver (algebraicClosure k K) K := isCurveOver_fullConstants k K
  have heft : Algebra.EssFiniteType (algebraicClosure k K) K :=
    Algebra.EssFiniteType.of_comp k (algebraicClosure k K) K
  exact AlgebraicCurve.exists_divisor_degree_one_of_finite_constants
    (exists_transcendental_finite_fullConstants k K) (constantsAreBase_fullConstants k K)

end FunctionField
