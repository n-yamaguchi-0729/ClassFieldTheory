/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Tactic.Ring
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.FiniteIntegerModule

/-!
# Divisors and degrees of all-place idele norms

The local order formula follows from preservation of integral units, the actual
ramification of the completion map, and the proved completed degree formula `ef`.
It identifies the divisor of an idele norm with divisor pushforward and therefore
preserves degree relative to the same constant field.
-/

open scoped AlgebraicCurve.Place WithZero

noncomputable section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

theorem localOrder_completionMap (w : AlgebraicCurve.Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    (localOrder w (Units.map
      (algebraMap (w.restrict K).adicCompletion w.adicCompletion) x)).toAdd =
      (w.ramificationIndex K : ℤ) * (localOrder (w.restrict K) x).toAdd := by
  change -WithZero.log (Valued.v
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion
      (x : (w.restrict K).adicCompletion))) =
    (w.ramificationIndex K : ℤ) * -WithZero.log (Valued.v (x :
      (w.restrict K).adicCompletion))
  rw [AlgebraicCurve.Place.algebraMap_adicCompletionComap_eq,
    AlgebraicCurve.Place.valued_adicCompletionComap, WithZero.log_pow, nsmul_eq_mul]
  ring

/-- The local norm formula from finiteness of the actual integer-ring extension. -/
theorem localOrder_localNorm_of_finite_integers (w : AlgebraicCurve.Place k L)
    [Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers]
    (x : w.adicCompletionˣ) :
    (localOrder (w.restrict K) (localNorm (K := K) w x)).toAdd =
      (w.inertiaDeg K : ℤ) * (localOrder w x).toAdd := by
  let π : (w.restrict K).adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K) 1
  have hπ : (localOrder (w.restrict K) π).toAdd = 1 :=
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection _ _ 1
  let y : w.adicCompletionˣ :=
    Units.map (algebraMap (w.restrict K).adicCompletion w.adicCompletion) π
  have hy : (localOrder w y).toAdd = (w.ramificationIndex K : ℤ) := by
    rw [localOrder_completionMap, hπ, mul_one]
  have hNy : (localOrder (w.restrict K) (localNorm (K := K) w y)).toAdd =
      (Module.finrank (w.restrict K).adicCompletion w.adicCompletion : ℤ) := by
    have hnorm : localNorm (K := K) w y =
        π ^ Module.finrank (w.restrict K).adicCompletion w.adicCompletion := by
      apply Units.ext
      exact Algebra.norm_algebraMap (π : (w.restrict K).adicCompletion)
    rw [hnorm, map_pow, toAdd_pow, hπ, nsmul_eq_mul, mul_one]
  let r : ℤ := (localOrder w x).toAdd
  let z : w.adicCompletionˣ := x ^ w.ramificationIndex K / y ^ r
  have hz : (localOrder w z).toAdd = 0 := by
    simp only [z, map_div, map_pow, map_zpow, toAdd_div, toAdd_pow, toAdd_zpow,
      nsmul_eq_mul, zsmul_eq_mul, hy]
    change (w.ramificationIndex K : ℤ) * r - r * (w.ramificationIndex K : ℤ) = 0
    ring
  have hNz : (localOrder (w.restrict K) (localNorm (K := K) w z)).toAdd = 0 :=
    (localOrder_eq_zero_iff _ _).2
      (localNorm_mem_localUnits w z ((localOrder_eq_zero_iff w z).1 hz))
  have heq : (w.ramificationIndex K : ℤ) *
      (localOrder (w.restrict K) (localNorm (K := K) w x)).toAdd -
        r * (Module.finrank (w.restrict K).adicCompletion w.adicCompletion : ℤ) = 0 := by
    simpa only [z, map_div, map_pow, map_zpow, toAdd_div, toAdd_pow, toAdd_zpow,
      nsmul_eq_mul, zsmul_eq_mul, hNy, Int.cast_id, id_def] using hNz
  rw [AlgebraicCurve.Place.finrank_adicCompletion_restrict_of_finite_integers] at heq
  have he : (w.ramificationIndex K : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (ne_of_gt w.ramificationIndex_pos)
  apply mul_left_cancel₀ he
  calc
    (w.ramificationIndex K : ℤ) *
        (localOrder (w.restrict K) (localNorm (K := K) w x)).toAdd =
        r * ((w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ)) :=
      sub_eq_zero.mp heq
    _ = (w.ramificationIndex K : ℤ) *
        ((w.inertiaDeg K : ℤ) * (localOrder w x).toAdd) := by
      change (localOrder w x).toAdd *
        ((w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ)) = _
      ring

/-- The order of a local norm for any finite extension of global function fields. -/
theorem localOrder_localNorm_of_finite [Finite k]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (w : AlgebraicCurve.Place k L) (x : w.adicCompletionˣ) :
    (localOrder (w.restrict K) (localNorm (K := K) w x)).toAdd =
      (w.inertiaDeg K : ℤ) * (localOrder w x).toAdd := by
  have : Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    moduleFinite_adicCompletionIntegers w
  exact localOrder_localNorm_of_finite_integers w x

private theorem localOrder_localNormOver_of_finite_integers (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L)
    [Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers]
    (hw : w.restrict K = v) (x : w.adicCompletionˣ) :
    (localOrder v (localNormOver v w hw x)).toAdd =
      (w.inertiaDeg K : ℤ) * (localOrder w x).toAdd := by
  subst v
  exact localOrder_localNorm_of_finite_integers w x

/-- The actual idele norm induces the existing inertia-weighted divisor pushforward. -/
theorem divisor_norm_of_finite_integers
    [∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers]
    (a : IdeleGroup k L) :
    (divisor (k := k) (K := K) (norm (K := K) (L := L) a)).toAdd =
      AlgebraicCurve.Divisor.pushforward K (divisor (k := k) (K := L) a).toAdd := by
  classical
  let D : AlgebraicCurve.Divisor k L := (divisor (k := k) (K := L) a).toAdd
  ext v
  rw [divisor_apply]
  change (localOrder v (normComponent (k := k) (K := K) (L := L) v a)).toAdd =
    AlgebraicCurve.Divisor.pushforward K D v
  rw [normComponent_apply, map_prod, toAdd_prod, AlgebraicCurve.Divisor.pushforward_apply]
  calc
    (∑ w : v.fiberOver L, (localOrder v
        (localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2)
          (a w.1))).toAdd) =
        ∑ w : v.fiberOver L, D w.1 * (w.1.inertiaDeg K : ℤ) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [localOrder_localNormOver_of_finite_integers, mul_comm]
      rfl
    _ = ∑ w ∈ v.fiberOver L, D w * (w.inertiaDeg K : ℤ) :=
      Finset.sum_attach (v.fiberOver L) (fun w => D w * (w.inertiaDeg K : ℤ))
    _ = ∑ w ∈ v.fiberOver L,
        (if w.restrict K = v then D w * (w.inertiaDeg K : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [ite_eq_left ((AlgebraicCurve.Place.mem_fiberOver v).mp hw)]
    _ = ∑ w ∈ D.support ∪ v.fiberOver L,
        (if w.restrict K = v then D w * (w.inertiaDeg K : ℤ) else 0) := by
      refine Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_
      rw [ite_eq_right (fun h => hw ((AlgebraicCurve.Place.mem_fiberOver v).mpr h))]
    _ = ∑ w ∈ D.support,
        (if w.restrict K = v then D w * (w.inertiaDeg K : ℤ) else 0) := by
      refine (Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_).symm
      rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]

/-- Norm preserves the idele degree measured over the same constant field. -/
theorem degree_norm_of_finite_integers
    [∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers]
    (a : IdeleGroup k L) :
    degree (k := k) (K := K) (norm (K := K) (L := L) a) = degree (k := k) (K := L) a := by
  apply Multiplicative.ext
  change AlgebraicCurve.Divisor.degree
      (divisor (k := k) (K := K) (norm (K := K) (L := L) a)).toAdd =
    AlgebraicCurve.Divisor.degree (divisor (k := k) (K := L) a).toAdd
  rw [divisor_norm_of_finite_integers, AlgebraicCurve.Divisor.degree_pushforward]

/-- Divisors commute with the norm of every finite function-field extension. -/
theorem divisor_norm_of_finite [Finite k]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (a : IdeleGroup k L) :
    (divisor (k := k) (K := K) (norm (K := K) (L := L) a)).toAdd =
      AlgebraicCurve.Divisor.pushforward K (divisor (k := k) (K := L) a).toAdd := by
  have : ∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    fun w => moduleFinite_adicCompletionIntegers w
  exact divisor_norm_of_finite_integers a

/-- Every finite idele norm preserves degree over the original constant field. -/
theorem degree_norm_of_finite [Finite k]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (a : IdeleGroup k L) :
    degree (k := k) (K := K) (norm (K := K) (L := L) a) =
      degree (k := k) (K := L) a := by
  have : ∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    fun w => moduleFinite_adicCompletionIntegers w
  exact degree_norm_of_finite_integers a

variable [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The order of a local norm is its source order times the actual inertia degree. -/
theorem localOrder_localNorm (w : AlgebraicCurve.Place k L) (x : w.adicCompletionˣ) :
    (localOrder (w.restrict K) (localNorm (K := K) w x)).toAdd =
      (w.inertiaDeg K : ℤ) * (localOrder w x).toAdd := by
  have : Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    AlgebraicCurve.Place.moduleFinite_adicCompletionIntegers_of_isSeparable w
  exact localOrder_localNorm_of_finite_integers w x

/-- The actual idele norm induces the existing inertia-weighted divisor pushforward. -/
theorem divisor_norm (a : IdeleGroup k L) :
    (divisor (k := k) (K := K) (norm (K := K) (L := L) a)).toAdd =
      AlgebraicCurve.Divisor.pushforward K (divisor (k := k) (K := L) a).toAdd := by
  have : ∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    fun w => AlgebraicCurve.Place.moduleFinite_adicCompletionIntegers_of_isSeparable w
  exact divisor_norm_of_finite_integers a

/-- Norm preserves the idele degree measured over the same constant field. -/
@[simp]
theorem degree_norm (a : IdeleGroup k L) :
    degree (k := k) (K := K) (norm (K := K) (L := L) a) =
      degree (k := k) (K := L) a := by
  have : ∀ w : AlgebraicCurve.Place k L,
      Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    fun w => AlgebraicCurve.Place.moduleFinite_adicCompletionIntegers_of_isSeparable w
  exact degree_norm_of_finite_integers a

end IdeleGroup

namespace IdeleClassGroup

variable [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The quotient norm also preserves the degree of an idele class. -/
@[simp]
theorem degree_norm (c : IdeleClassGroup k L) :
    degree (k := k) (K := K) (norm (K := K) (L := L) c) = degree (k := k) (K := L) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  change IdeleGroup.degree (k := k) (K := K) (IdeleGroup.norm (K := K) (L := L) a) =
    IdeleGroup.degree (k := k) (K := L) a
  exact IdeleGroup.degree_norm a

end IdeleClassGroup

end FunctionField
