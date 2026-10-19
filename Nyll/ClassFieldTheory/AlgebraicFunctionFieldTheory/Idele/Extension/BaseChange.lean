/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Filter.Cofinite
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDeg
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Inclusion of ideles under an arbitrary finite extension

The component above a place is the existing map between its completions. The
inverse image of the finite exceptional set is finite because restriction has
finite fibers, including in inseparable extensions. The resulting injective idele
homomorphism respects diagonal elements and induces a homomorphism on idele classes.

Local orders transform by ramification indices. Thus the idele divisor becomes
the existing divisor pullback. For a separable extension, its degree is multiplied
by the field degree. The latter uses the proved ramification-inertia identity,
not an additional hypothesis about degrees or places.
-/

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

/-- Inclusion of multiplicative groups through the actual map of completions. -/
def localBaseChange (w : AlgebraicCurve.Place k L) :
    (w.restrict K).adicCompletionˣ →* w.adicCompletionˣ :=
  Units.map (algebraMap (w.restrict K).adicCompletion w.adicCompletion).toMonoidHom

/-- A local integral unit remains an integral unit in an extending completion. -/
theorem localBaseChange_mem_localUnits (w : AlgebraicCurve.Place k L)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : x ∈ (w.restrict K).adicCompletionIntegers.units) :
    localBaseChange (K := K) w x ∈ w.adicCompletionIntegers.units := by
  apply (localOrder_eq_zero_iff w _).1
  change (localOrder w (Units.map
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion) x)).toAdd = 0
  rw [localOrder_completionMap, (localOrder_eq_zero_iff _ x).2 hx, mul_zero]

/-- Restriction of places takes the cofinite filter to the cofinite filter,
because each actual fiber of extending places is finite. -/
theorem tendsto_restrict_cofinite :
    Filter.Tendsto (fun w : AlgebraicCurve.Place k L => w.restrict K)
      Filter.cofinite Filter.cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  exact (AlgebraicCurve.Place.finite_setOf_restrict_eq (F' := L) v).to_subtype

/-- The all-place idele inclusion for an arbitrary finite extension. -/
def baseChange : IdeleGroup k K →* IdeleGroup k L :=
  RestrictedProduct.mapAlongMonoidHom
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
    (fun w : AlgebraicCurve.Place k L => w.adicCompletionˣ)
    (B₁ := fun v => v.adicCompletionIntegers.units)
    (B₂ := fun w => w.adicCompletionIntegers.units)
    (fun w => w.restrict K) (tendsto_restrict_cofinite (k := k) (K := K) (L := L))
    (localBaseChange (K := K))
    (Filter.Eventually.of_forall fun w x hx => localBaseChange_mem_localUnits w x hx)

@[simp]
theorem component_baseChange (w : AlgebraicCurve.Place k L) (a : IdeleGroup k K) :
    component w (baseChange (k := k) (K := K) (L := L) a) =
      localBaseChange (K := K) w (a (w.restrict K)) :=
  rfl

/-- Every base place has an extension, so the idele inclusion is injective. -/
theorem baseChange_injective :
    Function.Injective (baseChange (k := k) (K := K) (L := L)) := by
  intro a b hab
  apply RestrictedProduct.ext
  intro v
  obtain ⟨w, rfl⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := L) v
  have hcomp := congrArg (component w) hab
  rw [component_baseChange, component_baseChange] at hcomp
  exact Units.map_injective
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion).injective hcomp

variable [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Inclusion of ideles induces the ramification-weighted pullback of divisors. -/
theorem divisor_baseChange (a : IdeleGroup k K) :
    divisor (k := k) (K := L) (baseChange (k := k) (K := K) (L := L) a) =
      Multiplicative.ofAdd
        (AlgebraicCurve.Divisor.pullback L (divisor (k := k) (K := K) a).toAdd) := by
  apply Multiplicative.ext
  rw [toAdd_ofAdd]
  ext w
  rw [divisor_apply, AlgebraicCurve.Divisor.pullback_apply, divisor_apply]
  exact localOrder_completionMap w (a (w.restrict K))

/-- Idele degree is multiplied by the field degree under inclusion. -/
theorem degree_baseChange [Algebra.IsSeparable K L] (a : IdeleGroup k K) :
    (degree (k := k) (K := L) (baseChange (k := k) (K := K) (L := L) a)).toAdd =
      (Module.finrank K L : ℤ) * (degree (k := k) (K := K) a).toAdd := by
  have : AlgebraicCurve.SumRamificationInertia k K L :=
    ⟨fun v => AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (F' := L) v⟩
  have : AlgebraicCurve.FundamentalIdentity k K L :=
    AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  rw [degree_apply, divisor_baseChange]
  exact AlgebraicCurve.Divisor.degree_pullback (F' := L)
    (divisor (k := k) (K := K) a).toAdd

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The diagonal idele of a function maps to the diagonal idele of its field image. -/
@[simp]
theorem baseChange_principalIdele (x : Kˣ) :
    baseChange (k := k) (K := K) (L := L) (principalIdele k K x) =
      principalIdele k L (Units.map (algebraMap K L) x) := by
  apply RestrictedProduct.ext
  intro w
  apply Units.ext
  change algebraMap (w.restrict K).adicCompletion w.adicCompletion
      (algebraMap K (w.restrict K).adicCompletion (x : K)) =
    algebraMap L w.adicCompletion (algebraMap K L (x : K))
  exact (AlgebraicCurve.Place.adicCompletionComap_algebraMap_algebraMap
    K w (x : K)).symm

/-- Inclusion carries the actual subgroup of principal ideles to principal ideles. -/
theorem baseChange_mem_principalSubgroup {a : IdeleGroup k K}
    (ha : a ∈ principalSubgroup k K) :
    baseChange (k := k) (K := K) (L := L) a ∈ principalSubgroup k L := by
  obtain ⟨x, hx⟩ := (MonoidHom.mem_range (f := principalIdele k K)).mp ha
  apply (MonoidHom.mem_range (f := principalIdele k L)).mpr
  refine ⟨Units.map (algebraMap K L).toMonoidHom x, ?_⟩
  exact (baseChange_principalIdele (k := k) (K := K) (L := L) x).symm.trans
    (congrArg (baseChange (k := k) (K := K) (L := L)) hx)

end IdeleGroup

namespace IdeleClassGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The homomorphism of idele classes induced by field inclusion. -/
def baseChange : IdeleClassGroup k K →* IdeleClassGroup k L :=
  QuotientGroup.map (IdeleGroup.principalSubgroup k K) (IdeleGroup.principalSubgroup k L)
    (IdeleGroup.baseChange (k := k) (K := K) (L := L))
    (fun a ha => IdeleGroup.baseChange_mem_principalSubgroup
      (k := k) (K := K) (L := L) (a := a) ha)

@[simp]
theorem baseChange_mk (a : IdeleGroup k K) :
    baseChange (k := k) (K := K) (L := L) (mk (k := k) (K := K) a) =
      mk (k := k) (K := L) (IdeleGroup.baseChange (k := k) (K := K) (L := L) a) :=
  rfl

/-- The degree formula persists after passage to idele classes. -/
theorem degree_baseChange [Algebra.IsSeparable K L] (c : IdeleClassGroup k K) :
    (degree (k := k) (K := L) (baseChange (k := k) (K := K) (L := L) c)).toAdd =
      (Module.finrank K L : ℤ) * (degree (k := k) (K := K) c).toAdd := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [baseChange_mk, degree_mk, degree_mk]
  exact IdeleGroup.degree_baseChange (k := k) (K := K) (L := L) a

end IdeleClassGroup

end FunctionField
