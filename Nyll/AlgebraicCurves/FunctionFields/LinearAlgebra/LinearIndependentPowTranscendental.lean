/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_linearIndependent_pow_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Algebraic.Basic

/-! # Linear independence of powers of a transcendental element -/

open scoped Polynomial

namespace AlgebraicCurve

theorem linearIndependent_pow_of_transcendental
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx
  have hXj : LinearIndependent K (fun j : ℕ => (Polynomial.X : K[X]) ^ j) := by
    simpa only [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow] using
      (Polynomial.basisMonomials K).linearIndependent
  have heq : (fun j : ℕ => x ^ j) =
      (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (Polynomial.X ^ j)) := by
    funext j
    rw [map_pow, Polynomial.aeval_X]
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

end AlgebraicCurve
