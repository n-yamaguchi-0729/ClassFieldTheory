/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteFiniteCoordinates
import Nyll.ProCGroups.Topologies.FiniteQuotientLift

/-!
# Continuous absolute function-field reciprocity

The compatible finite Artin maps assemble into a continuous homomorphism
from the usual idele-class group to the topological abelianization of the
absolute Galois group. Its range is dense. Its kernel is the intersection
of the actual norms from the finite abelian fixed fields.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Absolute reciprocity, continuous for the usual idele-class and Krull quotient topologies. -/
def absoluteArtin : IdeleClassGroup k K →ₜ* localAbsoluteAbelianProfinite K :=
  ProCGroups.liftFiniteQuotients (localAbsoluteAbelianProfinite K)
    (absoluteFiniteArtinCoordinate k K) (absoluteFiniteArtinCoordinate_transition k K)

/-- Every finite projection of absolute reciprocity is its actual finite Artin coordinate. -/
theorem absoluteArtin_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (c : IdeleClassGroup k K) :
    (QuotientGroup.mk (absoluteArtin k K c) : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) =
      absoluteFiniteArtinCoordinate k K N c :=
  ProCGroups.liftFiniteQuotients_projection (localAbsoluteAbelianProfinite K)
    (absoluteFiniteArtinCoordinate k K) (absoluteFiniteArtinCoordinate_transition k K) N c

/-- The absolute function-field Artin homomorphism has dense range. -/
theorem absoluteArtin_denseRange : DenseRange (absoluteArtin k K) :=
  ProCGroups.liftFiniteQuotients_denseRange (localAbsoluteAbelianProfinite K)
    (absoluteFiniteArtinCoordinate k K) (absoluteFiniteArtinCoordinate_transition k K)
    (absoluteFiniteArtinCoordinate_surjective k K)

/-- Absolute reciprocity vanishes exactly on all finite abelian fixed-field norm subgroups. -/
theorem absoluteArtin_eq_one_iff_forall_finite_norm (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    absoluteArtin k K c = 1 ↔
      ∀ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
        c ∈ (IdeleClassGroup.norm (k := k) (K := K)
          (L := absoluteFiniteQuotientField K N)).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  exact (ProCGroups.liftFiniteQuotients_eq_one_iff (localAbsoluteAbelianProfinite K)
      (absoluteFiniteArtinCoordinate k K) (absoluteFiniteArtinCoordinate_transition k K) c).trans
    (forall_congr' (fun N => absoluteFiniteArtinCoordinate_eq_one_iff_mem_norm k K N c))

end FunctionField
