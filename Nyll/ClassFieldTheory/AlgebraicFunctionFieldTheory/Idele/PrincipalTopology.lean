/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.ValuationTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ProductFormula
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology

/-!
# Discreteness and closedness of principal ideles

An everywhere-integral principal idele represented by `x` has `x - 1` integral at
every place. If `x - 1` has positive order at one place, the product formula forces
`x = 1`: otherwise its principal divisor would have positive degree. This gives an
open neighbourhood isolating the identity in the principal subgroup.

The argument works over every perfect constant field and includes all places.
-/

open scoped WithZero

noncomputable section

namespace FunctionField.IdeleGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  [AlgebraicCurve.HasPrincipalDivisors k K]

private theorem eq_one_of_integral_and_near_one (v : AlgebraicCurve.Place k K)
    [Module.Finite k v.ResidueField] (x : Kˣ)
    (hint : ∀ w : AlgebraicCurve.Place k K,
      principalIdele k K x w ∈ w.adicCompletionIntegers.units)
    (hsmall : Valued.v (algebraMap K v.adicCompletion (x : K) - 1) < (1 : ℤᵐ⁰)) :
    x = 1 := by
  classical
  by_contra hne
  have hy : (x : K) - 1 ≠ 0 := by
    intro h
    exact hne (Units.ext (sub_eq_zero.mp h))
  have hnonneg (w : AlgebraicCurve.Place k K) : 0 ≤ w.ord ((x : K) - 1) := by
    have hxord : w.ord (x : K) = 0 := by
      rw [← localOrder_algebraMap w x]
      exact (localOrder_eq_zero_iff w _).2 (hint w)
    exact w.ord_nonneg_of_mem
      (w.toValuationSubring.sub_mem
        (w.mem_of_ord_nonneg x.ne_zero hxord.ge) w.toValuationSubring.one_mem)
  have hval : v.adicValuation ((x : K) - 1) < 1 := by
    have hv : Valued.v (algebraMap K v.adicCompletion ((x : K) - 1)) =
        v.adicValuation ((x : K) - 1) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (K := K) v.heightOneSpectrum ((x : K) - 1)
    rw [map_sub, map_one] at hv
    exact hv ▸ hsmall
  have hpos : 0 < v.ord ((x : K) - 1) := by
    change 0 < -WithZero.log (v.adicValuation ((x : K) - 1))
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (v.adicValuation_ne_zero hy),
      WithZero.exp_zero]
    exact hval
  have hzero : v.ord ((x : K) - 1) = 0 :=
    FunctionField.ord_eq_zero_of_forall_ord_nonneg v hy hnonneg
  exact (ne_of_gt hpos) hzero

variable [PerfectField k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The principal ideles have the discrete subspace topology. -/
instance principalSubgroupDiscreteTopology : DiscreteTopology (principalSubgroup k K) := by
  classical
  have : AlgebraicCurve.IsCurveOver k K := FunctionField.isCurveOver k K
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  have : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  rw [discreteTopology_iff_isOpen_singleton_one]
  let U : Set (IdeleGroup k K) :=
    {a : IdeleGroup k K | ∀ w : AlgebraicCurve.Place k K,
      a w ∈ w.adicCompletionIntegers.units} ∩
      {a | Valued.v ((a v : v.adicCompletion) - 1) < (1 : ℤᵐ⁰)}
  have hball : IsOpen {y : v.adicCompletion | Valued.v y < (1 : ℤᵐ⁰)} := by
    simpa only [Valuation.restrict_lt_one_iff] using (Valued.isOpen_ball v.adicCompletion 1)
  have hsub : Continuous (fun a : IdeleGroup k K => (a v : v.adicCompletion) - 1) :=
    (Units.continuous_val.comp (componentContinuous v).continuous).sub continuous_const
  have hintegral : IsOpen {a : IdeleGroup k K | ∀ w : AlgebraicCurve.Place k K,
      a w ∈ w.adicCompletionIntegers.units} :=
    RestrictedProduct.DiscreteValuation.isOpen_integralSubgroup
      (fun w : AlgebraicCurve.Place k K => w.adicCompletion)
  have hU : IsOpen U := hintegral.inter (hball.preimage hsub)
  have hpre : (Subtype.val ⁻¹' U : Set (principalSubgroup k K)) = {1} := by
    ext p
    constructor
    · intro hp
      change (p : IdeleGroup k K) ∈ U at hp
      obtain ⟨x, hx⟩ := p.property
      have hint : ∀ w : AlgebraicCurve.Place k K,
          principalIdele k K x w ∈ w.adicCompletionIntegers.units := by
        intro w
        rw [hx]
        exact hp.1 w
      have hsmall :
          Valued.v (algebraMap K v.adicCompletion (x : K) - 1) < (1 : ℤᵐ⁰) := by
        change Valued.v (((principalIdele k K x) v : v.adicCompletion) - 1) < 1
        rw [hx]
        exact hp.2
      have hxOne : x = 1 := eq_one_of_integral_and_near_one v x hint hsmall
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hx, hxOne, map_one]
      rfl
    · intro hp
      have hpOne : p = 1 := Set.mem_singleton_iff.mp hp
      subst p
      change (1 : IdeleGroup k K) ∈ U
      constructor
      · intro w
        exact w.adicCompletionIntegers.units.one_mem
      · change Valued.v ((1 : v.adicCompletion) - 1) < 1
        rw [sub_self, map_zero]
        exact zero_lt_one
  rw [← hpre]
  exact hU.preimage continuous_subtype_val

/-- The principal ideles form a closed subgroup of the all-place idele group. -/
theorem principalSubgroup_isClosed :
    IsClosed (principalSubgroup k K : Set (IdeleGroup k K)) :=
  Subgroup.isClosed_of_discreteTopology

end FunctionField.IdeleGroup
