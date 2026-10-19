/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.NumberTheory.FunctionField
import Mathlib.Order.Filter.Cofinite
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor

/-!
# Principal ideles and the function-field idele class group

The diagonal tuple of a nonzero function belongs to the restricted product because
its principal divisor has finite support. The divisor and degree maps therefore
recover the principal divisor and its degree zero. Injectivity uses an actual place,
constructed from a separating parameter over the perfect constant field; the chosen
rational-function-field presentation need not itself be separable.
-/

noncomputable section

namespace FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]


namespace IdeleGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The diagonal image of a nonzero function in all its completions. -/
def principalIdele : Kˣ →* IdeleGroup k K where
  toFun x := ⟨fun v => Units.map (algebraMap K v.adicCompletion) x, by
    obtain ⟨D, hD, _⟩ :=
      AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := k) (F := K) (x : K) x.ne_zero
    refine D.support.eventually_cofinite_notMem.mono ?_
    intro v hv
    apply (localOrder_eq_zero_iff v _).1
    rw [localOrder_algebraMap, ← hD v]
    exact Finsupp.notMem_support_iff.mp hv⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact (Units.map (algebraMap K v.adicCompletion).toMonoidHom).map_one
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro v
    exact (Units.map (algebraMap K v.adicCompletion).toMonoidHom).map_mul x y

variable {k K}

@[simp]
theorem component_principalIdele (v : AlgebraicCurve.Place k K) (x : Kˣ) :
    component v (principalIdele k K x) = Units.map (algebraMap K v.adicCompletion) x :=
  rfl

/-- The divisor of a diagonal idele is the principal divisor of its function. -/
@[simp]
theorem divisor_principalIdele_apply (x : Kˣ) (v : AlgebraicCurve.Place k K) :
    ((divisor (k := k) (K := K)) (principalIdele k K x)).toAdd v = v.ord (x : K) := by
  rw [divisor_apply (k := k) (K := K)]
  exact localOrder_algebraMap (k := k) (K := K) v x

/-- Principal ideles have degree zero, by the principal-divisor product formula. -/
@[simp]
theorem degree_principalIdele (x : Kˣ) : (degree (k := k) (K := K)) (principalIdele k K x) = 1 := by
  obtain ⟨D, hD, hdegree⟩ :=
    AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := k) (F := K) (x : K) x.ne_zero
  have hdiv : ((divisor (k := k) (K := K)) (principalIdele k K x)).toAdd = D := by
    ext v
    exact (divisor_principalIdele_apply x v).trans (hD v).symm
  apply Multiplicative.ext
  change AlgebraicCurve.Divisor.degree
    ((divisor (k := k) (K := K)) (principalIdele k K x)).toAdd = 0
  rw [hdiv]
  exact hdegree

variable (k K)

/-- The subgroup of diagonal ideles coming from nonzero rational functions. -/
def principalSubgroup : Subgroup (IdeleGroup k K) :=
  (principalIdele k K).range

variable [PerfectField k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Evaluation at an actual place proves that the diagonal map is injective. -/
theorem principalIdele_injective : Function.Injective (principalIdele k K) := by
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  intro x y h
  apply Units.map_injective (algebraMap K v.adicCompletion).injective
  exact congrArg (component v) h

/-- Nonzero rational functions, identified with their principal ideles. -/
def principalEquiv : Kˣ ≃* principalSubgroup k K :=
  MonoidHom.ofInjective (principalIdele_injective k K)

@[simp]
theorem coe_principalEquiv (x : Kˣ) :
    (principalEquiv k K x : IdeleGroup k K) = principalIdele k K x :=
  MonoidHom.ofInjective_apply (principalIdele_injective k K)

end IdeleGroup

/-- The idele class group, modulo the diagonal nonzero rational functions. -/
abbrev IdeleClassGroup [AlgebraicCurve.HasPrincipalDivisors k K] :=
  IdeleGroup k K ⧸ IdeleGroup.principalSubgroup k K

end FunctionField
