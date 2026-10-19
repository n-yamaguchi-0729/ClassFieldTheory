/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.Principal
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ProductFormula

/-!
# Discreteness and closedness of principal adeles

The product formula forces a nonzero function integral at every place to have
order zero. Intersecting the integral adeles with the strict unit ball at one
place therefore isolates zero in the diagonal additive subgroup. The principal
adeles form a discrete and closed subgroup for the all-place topology.
-/

open scoped WithZero

noncomputable section

namespace FunctionField.AdeleRing

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
  [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The additive subgroup of diagonal adeles represented by global functions. -/
def principalSubgroup : AddSubgroup (AdeleRing k K) :=
  (principalAdele k K).toAddMonoidHom.range

variable {k K}

private theorem eq_zero_of_integral_and_near_zero (v : AlgebraicCurve.Place k K)
    [Module.Finite k v.ResidueField] (x : K)
    (hint : principalAdele k K x ∈ integralSubring (k := k) (K := K))
    (hsmall : Valued.v (algebraMap K v.adicCompletion x) < (1 : ℤᵐ⁰)) : x = 0 := by
  by_contra hx
  have hnonneg (w : AlgebraicCurve.Place k K) : 0 ≤ w.ord x := by
    have hv : Valued.v (algebraMap K w.adicCompletion x) = w.adicValuation x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (K := K) w.heightOneSpectrum x
    have hmem := hint w
    change Valued.v (algebraMap K w.adicCompletion x) ≤ (1 : ℤᵐ⁰) at hmem
    change 0 ≤ -WithZero.log (w.adicValuation x)
    rw [neg_nonneg, WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx),
      WithZero.exp_zero]
    exact hv ▸ hmem
  have hv : Valued.v (algebraMap K v.adicCompletion x) = v.adicValuation x :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (K := K) v.heightOneSpectrum x
  have hpos : 0 < v.ord x := by
    change 0 < -WithZero.log (v.adicValuation x)
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (v.adicValuation_ne_zero hx),
      WithZero.exp_zero]
    exact hv ▸ hsmall
  exact (ne_of_gt hpos) (FunctionField.ord_eq_zero_of_forall_ord_nonneg v hx hnonneg)

variable [PerfectField k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The diagonal additive subgroup has the discrete subspace topology. -/
instance principalSubgroupDiscreteTopology : DiscreteTopology (principalSubgroup k K) := by
  classical
  have : AlgebraicCurve.IsCurveOver k K := FunctionField.isCurveOver k K
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  have : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  rw [discreteTopology_iff_isOpen_singleton_zero]
  let U : Set (AdeleRing k K) :=
    (integralSubring (k := k) (K := K) : Set (AdeleRing k K)) ∩
      {a | Valued.v (component v a) < (1 : ℤᵐ⁰)}
  have hball : IsOpen {y : v.adicCompletion | Valued.v y < (1 : ℤᵐ⁰)} := by
    simpa only [Valuation.restrict_lt_one_iff] using (Valued.isOpen_ball v.adicCompletion 1)
  have hU : IsOpen U :=
    isOpen_integralSubring.inter (hball.preimage (continuous_component v))
  have hpre : (Subtype.val ⁻¹' U : Set (principalSubgroup k K)) = {0} := by
    ext p
    constructor
    · intro hp
      change (p : AdeleRing k K) ∈ U at hp
      obtain ⟨x, hx⟩ := p.property
      change principalAdele k K x = (p : AdeleRing k K) at hx
      have hint : principalAdele k K x ∈ integralSubring (k := k) (K := K) := by
        rw [hx]
        exact hp.1
      have hsmall : Valued.v (algebraMap K v.adicCompletion x) < (1 : ℤᵐ⁰) := by
        rw [← component_principalAdele x v, hx]
        exact hp.2
      have hxZero : x = 0 := eq_zero_of_integral_and_near_zero v x hint hsmall
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hx, hxZero, map_zero]
      rfl
    · intro hp
      have hpZero : p = 0 := Set.mem_singleton_iff.mp hp
      subst p
      change (0 : AdeleRing k K) ∈ U
      constructor
      · exact (integralSubring (k := k) (K := K)).zero_mem
      · change Valued.v (component v 0) < (1 : ℤᵐ⁰)
        rw [map_zero, map_zero]
        exact zero_lt_one
  rw [← hpre]
  exact hU.preimage continuous_subtype_val

/-- Principal adeles form a closed additive subgroup of the adele ring. -/
theorem principalSubgroup_isClosed :
    IsClosed (principalSubgroup k K : Set (AdeleRing k K)) :=
  AddSubgroup.isClosed_of_discreteTopology

end FunctionField.AdeleRing
