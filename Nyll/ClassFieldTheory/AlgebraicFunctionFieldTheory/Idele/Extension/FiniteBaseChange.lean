/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.TypeTags.Basic
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.FiniteIntegerModule
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Inclusion and norm for arbitrary finite function-field extensions

The already proved principal norm formula, evaluated at a global uniformizer,
determines the sum of the actual completed degrees. The original completed
product computation then proves the inclusion-norm and degree formulas without
separability. No new degree identity is assumed.
-/

noncomputable section
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

namespace IdeleGroup

/-- The completed degrees over a place sum to the degree of any finite
function-field extension, including its inseparable part. -/
theorem sum_finrank_adicCompletion_of_finite (v : AlgebraicCurve.Place k K) :
    (∑ w : v.fiberOver L,
      Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion) =
        Module.finrank K L := by
  classical
  obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
  have hπzero : π ≠ 0 := by
    intro hz
    have hfalse : (0 : ℤ) = 1 := by
      simpa only [hz, AlgebraicCurve.Place.ord_zero] using hπ
    exact zero_ne_one hfalse
  let u : Kˣ := Units.mk0 π hπzero
  let a : IdeleGroup k K := principalIdele k K u
  have hnorm : norm (K := K) (L := L) (baseChange (K := K) (L := L) a) =
      a ^ Module.finrank K L := by
    change norm (K := K) (L := L)
        (baseChange (K := K) (L := L) (principalIdele k K u)) =
      (principalIdele k K u) ^ Module.finrank K L
    rw [baseChange_principalIdele, norm_principalIdele_of_finite, ← map_pow]
    apply congrArg (principalIdele k K)
    apply Units.ext
    exact Algebra.norm_algebraMap (R := K) (S := L) (u : K)
  have hcomponent := congrArg (component v) hnorm
  change normComponent (K := K) (L := L) v (baseChange (K := K) (L := L) a) =
      (a v) ^ Module.finrank K L at hcomponent
  rw [normComponent_baseChange] at hcomponent
  have horders := congrArg (fun x : v.adicCompletionˣ => (localOrder v x).toAdd) hcomponent
  have hua : (localOrder v (a v)).toAdd = 1 :=
    (localOrder_algebraMap v u).trans hπ
  simp only [map_pow, toAdd_pow, nsmul_eq_mul, hua, mul_one] at horders
  exact Int.natCast_inj.mp horders

/-- Ramification indices times inertia degrees sum to the actual finite
function-field degree, including the inseparable part. -/
theorem sum_ramificationIndex_mul_inertiaDeg_of_finite (v : AlgebraicCurve.Place k K) :
    (∑ w ∈ v.fiberOver L,
      (w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ)) =
        (Module.finrank K L : ℤ) := by
  classical
  calc
    (∑ w ∈ v.fiberOver L,
        (w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ)) =
      ∑ w : v.fiberOver L,
        (w.1.ramificationIndex K : ℤ) * (w.1.inertiaDeg K : ℤ) :=
      (Finset.sum_attach (v.fiberOver L)
        (fun w => (w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ))).symm
    _ = ∑ w : v.fiberOver L,
        (Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion : ℤ) := by
      apply Finset.sum_congr rfl
      intro w _
      have : Module.Finite (w.1.restrict K).adicCompletionIntegers
          w.1.adicCompletionIntegers := moduleFinite_adicCompletionIntegers w.1
      exact (AlgebraicCurve.Place.finrank_adicCompletion_restrict_of_finite_integers w.1).symm
    _ = (Module.finrank K L : ℤ) := by
      rw [← Nat.cast_sum, sum_finrank_adicCompletion_of_finite]

/-- Norm after inclusion is the extension-degree power for every finite extension. -/
theorem norm_baseChange_of_finite (a : IdeleGroup k K) :
    norm (K := K) (L := L) (baseChange (K := K) (L := L) a) =
      a ^ Module.finrank K L := by
  apply RestrictedProduct.ext
  intro v
  change normComponent (K := K) (L := L) v (baseChange (K := K) (L := L) a) =
    (a v) ^ Module.finrank K L
  rw [normComponent_baseChange, sum_finrank_adicCompletion_of_finite]

/-- Inclusion multiplies idele degree by the degree of any finite extension. -/
theorem degree_baseChange_of_finite (a : IdeleGroup k K) :
    (degree (k := k) (K := L) (baseChange (K := K) (L := L) a)).toAdd =
      (Module.finrank K L : ℤ) * (degree (k := k) (K := K) a).toAdd := by
  have h := congrArg (fun b : IdeleGroup k K => (degree (k := k) (K := K) b).toAdd)
    (norm_baseChange_of_finite (L := L) a)
  simpa only [degree_norm_of_finite, map_pow, toAdd_pow, nsmul_eq_mul] using h

end IdeleGroup

namespace IdeleClassGroup

/-- Norm after inclusion is the extension-degree power on actual idele classes. -/
theorem finiteNorm_baseChange (c : IdeleClassGroup k K) :
    finiteNorm (K := K) (L := L) (baseChange (K := K) (L := L) c) =
      c ^ Module.finrank K L := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [baseChange_mk]
  change mk (k := k) (K := K)
      (IdeleGroup.norm (k := k) (K := K) (L := L)
        (IdeleGroup.baseChange (k := k) (K := K) (L := L) a)) =
    (mk (k := k) (K := K) a) ^ Module.finrank K L
  rw [IdeleGroup.norm_baseChange_of_finite, map_pow]

/-- Inclusion multiplies class degree by the actual finite field degree. -/
theorem degree_baseChange_of_finite (c : IdeleClassGroup k K) :
    (degree (k := k) (K := L) (baseChange (K := K) (L := L) c)).toAdd =
      (Module.finrank K L : ℤ) * (degree (k := k) (K := K) c).toAdd := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact IdeleGroup.degree_baseChange_of_finite a

end IdeleClassGroup
end FunctionField
