/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The divisor class group as a quotient of the idele class group

The kernel is exactly the image of the everywhere-integral ideles. Over a finite
constant field this kernel is compact. The quotient is the existing full Picard
group; the degree direction is retained.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The image in the idele class group of the everywhere-integral ideles. -/
def integralSubgroup : Subgroup (IdeleClassGroup k K) :=
  (IdeleGroup.integralSubgroup (k := k) (K := K)).map (mk (k := k) (K := K))

/-- Divisor classes kill exactly the classes represented by integral ideles. -/
theorem divisorClass_ker :
    (divisorClass (k := k) (K := K)).ker = integralSubgroup (k := k) (K := K) := by
  ext c
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  change divisorClass (k := k) (K := K) (mk (k := k) (K := K) a) = 1 ↔ _
  rw [divisorClass_mk]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (IdeleGroup.divisorClass_eq_one_iff_exists_integral a).1 h
    refine ⟨a / IdeleGroup.principalIdele k K x, hx, ?_⟩
    have hp : mk (k := k) (K := K) (IdeleGroup.principalIdele k K x) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
    rw [map_div, hp, div_one]
  · rintro ⟨u, hu, huc⟩
    rw [← divisorClass_mk, ← huc, divisorClass_mk]
    have hd : IdeleGroup.divisor (k := k) (K := K) u = 1 :=
      (IdeleGroup.divisor_eq_one_iff u).2 hu
    change (QuotientAddGroup.mk (IdeleGroup.divisor (k := k) (K := K) u).toAdd :
      AlgebraicCurve.Pic k K) = 0
    rw [hd]
    exact map_zero (QuotientAddGroup.mk' AlgebraicCurve.Divisor.principal)

/-- Normality follows from the proved kernel description with the existing quotient
group structure. -/
instance integralSubgroup_normal : (integralSubgroup (k := k) (K := K)).Normal := by
  rw [← divisorClass_ker]
  infer_instance

/-- Modding out integral idele classes gives the divisor class group. -/
def quotientIntegralSubgroupEquivPic :
    IdeleClassGroup k K ⧸ integralSubgroup (k := k) (K := K) ≃*
      Multiplicative (AlgebraicCurve.Pic k K) :=
  (QuotientGroup.quotientMulEquivOfEq (divisorClass_ker (k := k) (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (divisorClass (k := k) (K := K))
      divisorClass_surjective)

/-- The kernel of the divisor-class map is compact over a finite constant field. -/
theorem isCompact_integralSubgroup [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    IsCompact (integralSubgroup (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  change IsCompact ((mk (k := k) (K := K)) ''
    (IdeleGroup.integralSubgroup (k := k) (K := K) : Set (IdeleGroup k K)))
  exact IdeleGroup.isCompact_integralSubgroup.image QuotientGroup.continuous_mk

end FunctionField.IdeleClassGroup
