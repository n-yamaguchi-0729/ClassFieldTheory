/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Ext
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Tactic.Ring
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Finite
import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Divisor classes under enlargement of the constant field

For a finite extension of constants inside the same function field, the actual places are
identified by `Place.constantFieldEquiv`. Reindexing the existing divisors preserves principal
divisors and multiplies degrees by the nonzero constant-field degree. It therefore identifies
the degree-zero divisor class groups.

For the full constant field `algebraicClosure k K`, the established regular-function criterion
and curve structure supply Riemann--Roch finiteness. The equivalence then gives finiteness of
`Pic0 k K` for every function field over a finite base, without an extra constants hypothesis.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve



variable (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The degree-zero divisor class group of any function field over a finite field is finite. -/
theorem finite_pic0 : Finite (Pic0 k K) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have : IsCurveOver (algebraicClosure k K) K := isCurveOver_fullConstants k K
  have : Algebra.EssFiniteType (algebraicClosure k K) K :=
    Algebra.EssFiniteType.of_comp k (algebraicClosure k K) K
  have : Finite (Pic0 (algebraicClosure k K) K) :=
    AlgebraicCurve.finite_pic0_of_isCurveOver (algebraicClosure k K) K
      (constantsAreBase_fullConstants k K)
  exact Finite.of_injective (pic0ConstantEquiv k (algebraicClosure k K) K)
    (pic0ConstantEquiv k (algebraicClosure k K) K).injective

end FunctionField
