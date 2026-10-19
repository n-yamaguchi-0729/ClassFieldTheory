/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendentalPerfectField
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental
import Nyll.AlgebraicCurves.Places.Orders.BasicTranscendental

/-!
# Function fields and the all-place curve API

A finite extension of a rational function field over a perfect field satisfies the existing
`AlgebraicCurve.IsCurveOver` condition. The chosen rational parameter need not be separating:
the curve theorem constructs a separating parameter from perfectness. Over a finite base field,
every place therefore has a finite residue field, including places above infinity.
-/

namespace FunctionField

variable (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- Mathlib's function field over a perfect field has principal divisors, finite-dimensional
residue fields and a one-dimensional module of differentials. -/
theorem isCurveOver [PerfectField k] : AlgebraicCurve.IsCurveOver k K := by
  have htr : Transcendental k (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := K)
      (algebraMap (RatFunc k) K).injective).2 (RatFunc.transcendental_X (K := k))
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr
    (FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K))

/-- The residue field of every place of a function field over a finite field is finite. -/
theorem finite_residueField [Finite k] (v : AlgebraicCurve.Place k K) :
    Finite v.ResidueField := by
  have : AlgebraicCurve.IsCurveOver k K := isCurveOver k K
  have : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  exact Module.finite_of_finite k

/-- A one-variable function field over a perfect field has a place, independently
of whether the chosen rational-function-field presentation is separable. -/
theorem nonempty_place [PerfectField k] :
    Nonempty (AlgebraicCurve.Place k K) := by
  have htr : Transcendental k (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := K)
      (algebraMap (RatFunc k) K).injective).2 (RatFunc.transcendental_X (K := k))
  obtain ⟨t, ht, htfin, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr
      (FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K))
  have : Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set K)) K := htsep
  exact AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional k t ht htfin

end FunctionField
