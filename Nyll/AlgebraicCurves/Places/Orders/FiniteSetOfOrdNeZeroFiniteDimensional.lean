/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Orders.PositiveOrderElement
public import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteSetOfOrdNeZero
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.RatFunc.Basic
public import Nyll.AlgebraicCurves.Places.Orders.MinpolyCoefficientOrder

/-!
# Finite setOf ord ne zero of finiteDimensional

A function in a finite extension of a rational function field has nonzero order at only finitely
many places.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Finite_setOf_ord_ne_zero_of_finiteDimensional

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding exists_ord_pos

section SupportTransfer

open Polynomial

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0)
  (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 :=
  _root_.AlgebraicCurve.Place.exists_minpoly_coeff_ord_ne_zero (F := F) w hf hford

open _root_.AlgebraicCurve.Place
end SupportTransfer

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional {K F' : Type*}
  [Field K] [Field F'] [Algebra K F']
    [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
      [Algebra.IsSeparable (RatFunc K) F']
    {f : F'} (hf : f ≠ 0) : {w : Place K F' | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · simp only [h0, Place.ord_zero, ne_self_iff_false, Set.ofPred_false, Set.finite_empty]
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  · intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]
end AlgebraicCurves.Places.Proofs.Finite_setOf_ord_ne_zero_of_finiteDimensional
end ProofImplementation
