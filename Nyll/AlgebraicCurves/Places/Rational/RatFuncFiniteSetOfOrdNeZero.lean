/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.RatFuncSubsingletonSetOfNeOfHeightOneSpectrum

/-!
# RationalFunctionField finite setOf ord ne zero

A nonzero rational function has nonzero order at only finitely many places.
-/

namespace AlgebraicCurve.RationalFunctionField

open IsDedekindDomain
open scoped Polynomial

variable {K : Type*} [Field K]

private theorem finite_setOf_valuation_ne_one' {f : RatFunc K} (hf : f ≠ 0) :
    {w : HeightOneSpectrum K[X] | w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

theorem finite_setOf_ord_ne_zero {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K))
        (finite_setOf_valuation_ne_one' hf))
      (Set.Subsingleton.finite subsingleton_setOf_forall_ne_ofHeightOneSpectrum))
    fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
  by_cases hcase : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hcase
    refine Or.inl ⟨w, fun hone => hv ?_, rfl⟩
    exact ((Place.ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hf).mpr
      ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := RatFunc K)
        w).eq_one_iff_eq_one.mp hone)
  · exact Or.inr fun w h => hcase ⟨w, h⟩

end AlgebraicCurve.RationalFunctionField
