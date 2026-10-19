/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDeg
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology

/-!
# Continuity and norm of idele inclusion

The existing continuous completion maps induce the continuous restricted-product
inclusion for arbitrary finite extensions. In a separable extension its composition
with norm raises each idele to the extension degree:
the local norm of an included component is its completed-degree power, and the
completed degrees sum to the original field degree over the actual place fiber.
Both statements descend to the quotient by principal ideles.
-/

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

/-- The inclusion on local multiplicative groups is continuous. -/
theorem continuous_localBaseChange (w : AlgebraicCurve.Place k L) :
    Continuous (localBaseChange (K := K) w) := by
  have hmap : Continuous
      (algebraMap (w.restrict K).adicCompletion w.adicCompletion) := by
    rw [AlgebraicCurve.Place.algebraMap_adicCompletionComap_eq]
    exact AlgebraicCurve.Place.continuous_adicCompletionComap K w
  exact hmap.units_map
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion).toMonoidHom

/-- The all-place inclusion is continuous for the restricted-product topologies. -/
theorem continuous_baseChange :
    Continuous (baseChange (k := k) (K := K) (L := L)) := by
  exact RestrictedProduct.mapAlong_continuous
    (fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
    (fun w : AlgebraicCurve.Place k L => w.adicCompletionˣ)
    (A₁ := fun v => (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))
    (A₂ := fun w => (w.adicCompletionIntegers.units : Set w.adicCompletionˣ))
    (fun w => w.restrict K) (tendsto_restrict_cofinite (k := k) (K := K) (L := L))
    (fun w => localBaseChange (K := K) w)
    (Filter.Eventually.of_forall fun w x hx => localBaseChange_mem_localUnits w x hx)
    continuous_localBaseChange

private theorem localNormOver_baseChange (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v) (a : IdeleGroup k K) :
    localNormOver v w hw ((baseChange (k := k) (K := K) (L := L) a) w) =
      (a v) ^ Module.finrank (w.restrict K).adicCompletion w.adicCompletion := by
  subst v
  apply Units.ext
  change Algebra.norm (w.restrict K).adicCompletion
      (algebraMap (w.restrict K).adicCompletion w.adicCompletion
        (a (w.restrict K) : (w.restrict K).adicCompletion)) =
    (a (w.restrict K) : (w.restrict K).adicCompletion) ^
      Module.finrank (w.restrict K).adicCompletion w.adicCompletion
  exact Algebra.norm_algebraMap (a (w.restrict K) : (w.restrict K).adicCompletion)

/-- At one base place, norm after inclusion raises the component to the sum
of the actual completed extension degrees, without a separability assumption. -/
theorem normComponent_baseChange (v : AlgebraicCurve.Place k K) (a : IdeleGroup k K) :
    normComponent (k := k) (K := K) (L := L) v
        (baseChange (k := k) (K := K) (L := L) a) =
      (a v) ^ ∑ w : v.fiberOver L,
        Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion := by
  classical
  rw [normComponent_apply]
  calc
    (∏ w : v.fiberOver L, localNormOver v w.1
        ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2)
        ((baseChange (k := k) (K := K) (L := L) a) w.1)) =
      ∏ w : v.fiberOver L,
        (a v) ^ Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion :=
      Finset.prod_congr rfl fun w _ => localNormOver_baseChange v w.1
        ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) a
    _ = (a v) ^ ∑ w : v.fiberOver L,
        Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion :=
      Finset.prod_pow_eq_pow_sum _ _ _

section NormComposition

variable [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The degrees of the actual completed extensions add to the global extension degree. -/
theorem sum_finrank_adicCompletion (v : AlgebraicCurve.Place k K) :
    (∑ w : v.fiberOver L,
      Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion) =
        Module.finrank K L := by
  classical
  rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
  calc
    ∑ w : v.fiberOver L,
        (Module.finrank (w.1.restrict K).adicCompletion w.1.adicCompletion : ℤ) =
      ∑ w : v.fiberOver L,
        (w.1.ramificationIndex K : ℤ) * (w.1.inertiaDeg K : ℤ) :=
      Finset.sum_congr rfl fun w _ => AlgebraicCurve.Place.finrank_adicCompletion_restrict w.1
    _ = ∑ w ∈ v.fiberOver L,
        (w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ) :=
      Finset.sum_attach (v.fiberOver L)
        (fun w => (w.ramificationIndex K : ℤ) * (w.inertiaDeg K : ℤ))
    _ = (Module.finrank K L : ℤ) := by
      rw [← AlgebraicCurve.Place.fiber_eq_fiberOver v]
      exact AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (F' := L) v

/-- Norm after inclusion is the extension-degree power on all-place ideles. -/
theorem norm_baseChange (a : IdeleGroup k K) :
    norm (k := k) (K := K) (L := L) (baseChange (k := k) (K := K) (L := L) a) =
      a ^ Module.finrank K L := by
  classical
  apply RestrictedProduct.ext
  intro v
  change normComponent (k := k) (K := K) (L := L) v
      (baseChange (k := k) (K := K) (L := L) a) = (a v) ^ Module.finrank K L
  rw [normComponent_baseChange, sum_finrank_adicCompletion]

end NormComposition

end IdeleGroup

namespace IdeleClassGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The class map induced by inclusion is continuous for the quotient topologies. -/
theorem continuous_baseChange :
    Continuous (baseChange (k := k) (K := K) (L := L)) := by
  apply continuous_coinduced_dom.2
  exact QuotientGroup.continuous_mk.comp
    (IdeleGroup.continuous_baseChange (k := k) (K := K) (L := L))

/-- Norm after inclusion is also the extension-degree power on idele classes. -/
theorem norm_baseChange [Algebra.IsSeparable K L] (c : IdeleClassGroup k K) :
    norm (k := k) (K := K) (L := L) (baseChange (k := k) (K := K) (L := L) c) =
      c ^ Module.finrank K L := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [baseChange_mk]
  change mk (k := k) (K := K)
      (IdeleGroup.norm (k := k) (K := K) (L := L)
        (IdeleGroup.baseChange (k := k) (K := K) (L := L) a)) =
    (mk (k := k) (K := K) a) ^ Module.finrank K L
  rw [IdeleGroup.norm_baseChange, map_pow]

end IdeleClassGroup

end FunctionField
