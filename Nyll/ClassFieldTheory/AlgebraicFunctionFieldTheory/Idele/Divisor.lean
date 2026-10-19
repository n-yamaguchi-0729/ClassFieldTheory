/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# The divisor and degree of a function-field idele

All places, including the places above infinity, contribute to the divisor.
The normalized order construction is shared with the number-field ideal map.
The target is the existing curve divisor group, rather than a second copy of it.
-/

noncomputable section

open scoped WithZero

namespace FunctionField.IdeleGroup

open IsDedekindDomain

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Normalized order on the multiplicative group of the completed field. -/
abbrev localOrder (v : AlgebraicCurve.Place k K) :
    v.adicCompletionˣ →* Multiplicative ℤ :=
  RestrictedProduct.DiscreteValuation.localOrder v.adicCompletion

/-- Order zero characterizes the integral local units. -/
theorem localOrder_eq_zero_iff (v : AlgebraicCurve.Place k K)
    (x : v.adicCompletionˣ) :
    (localOrder v x).toAdd = 0 ↔ x ∈ v.adicCompletionIntegers.units :=
  RestrictedProduct.DiscreteValuation.localOrder_eq_zero_iff v.adicCompletion x

/-- Completion preserves the normalized order of a nonzero rational function. -/
@[simp]
theorem localOrder_algebraMap (v : AlgebraicCurve.Place k K) (x : Kˣ) :
    (localOrder v (Units.map (algebraMap K v.adicCompletion) x)).toAdd =
      v.ord (x : K) := by
  change -WithZero.log (Valued.v (algebraMap K v.adicCompletion (x : K))) =
    -WithZero.log (v.adicValuation (x : K))
  exact congrArg (fun z : ℤᵐ⁰ => -WithZero.log z)
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (K := K) v.heightOneSpectrum (x : K))

/-- The divisor of an idele, formed from its finitely supported local orders. -/
def divisor : IdeleGroup k K →* Multiplicative (AlgebraicCurve.Divisor k K) :=
  RestrictedProduct.DiscreteValuation.valuationVector
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)

@[simp]
theorem divisor_apply (a : IdeleGroup k K) (v : AlgebraicCurve.Place k K) :
    (divisor (k := k) (K := K) a).toAdd v = (localOrder v (a v)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVector_apply _ a v

/-- An idele has zero divisor exactly when every component is an integral unit. -/
theorem divisor_eq_one_iff (a : IdeleGroup k K) :
    divisor (k := k) (K := K) a = 1 ↔ ∀ v : AlgebraicCurve.Place k K,
      a v ∈ v.adicCompletionIntegers.units :=
  RestrictedProduct.DiscreteValuation.valuationVector_eq_one_iff _ a

/-- Every curve divisor is represented by an idele. -/
theorem divisor_surjective : Function.Surjective (divisor (k := k) (K := K)) :=
  RestrictedProduct.DiscreteValuation.valuationVector_surjective
    (fun v : AlgebraicCurve.Place k K => v.adicCompletion)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v.heightOneSpectrum)

/-- A local multiplicative element contributes only at its supporting place. -/
@[simp]
theorem divisor_placeIdele (v : AlgebraicCurve.Place k K) (x : v.adicCompletionˣ) :
    divisor (k := k) (K := K) (placeIdele v x) =
      Multiplicative.ofAdd (Finsupp.single v (localOrder v x).toAdd) := by
  classical
  apply Multiplicative.ext
  ext w
  rw [divisor_apply]
  change (localOrder w (component w (placeIdele v x))).toAdd =
    Finsupp.single v (localOrder v x).toAdd w
  by_cases h : w = v
  · subst w
    rw [component_placeIdele_same, Finsupp.single_eq_same]
  · rw [component_placeIdele_of_ne v w x h, map_one,
      Finsupp.single_eq_of_ne h]
    rfl

/-- The degree of an idele relative to the chosen constant field. -/
def degree : IdeleGroup k K →* Multiplicative ℤ :=
  AlgebraicCurve.Divisor.degree.toMultiplicative.comp divisor

@[simp]
theorem degree_apply (a : IdeleGroup k K) :
    (degree (k := k) (K := K) a).toAdd =
      AlgebraicCurve.Divisor.degree (divisor (k := k) (K := K) a).toAdd :=
  rfl

/-- The degree of a local idele is its order times the residue-field degree. -/
@[simp]
theorem degree_placeIdele (v : AlgebraicCurve.Place k K) (x : v.adicCompletionˣ) :
    (degree (k := k) (K := K) (placeIdele v x)).toAdd =
      (localOrder v x).toAdd * v.deg := by
  rw [degree_apply, divisor_placeIdele]
  exact AlgebraicCurve.Divisor.degree_single v (localOrder v x).toAdd

end FunctionField.IdeleGroup
