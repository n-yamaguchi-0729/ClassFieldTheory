/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimePowerRayBound
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierBoundedExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierBoundedClasses

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero

/-!
# Actual norm cofinality for characteristic-p ray-power subgroups

The bounded AS compositum contains the ray congruence in its norm image.
Its exponent-p Galois group also makes every pth power a norm. The actual
degree lower bound and the independently computed S-idele jet index force
the norm image into the prescribed ray-power subgroup.
-/

noncomputable section
open AlgebraicCurve
namespace FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- Every characteristic-p ray-power subgroup contains an actual finite
abelian norm subgroup in the fixed separable closure. -/
theorem exists_finiteAbelian_norm_le_powerRay_prime
    (p : ℕ) [Fact p.Prime] [CharP K p] (m₀ : RayClass.Modulus k K) :
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
    ∃ E : IntermediateField K (SeparableClosure K),
      ∃ (_ : FiniteDimensional K E) (_ : IsAbelianGalois K E),
        (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ≤
          RayClass.powerRaySubgroup m₀ p := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  obtain ⟨m, S, hm, _, _, hsupp, hindex⟩ := exists_primePowerRay_bound p m₀
  obtain ⟨E, hfinite, hab, hexp, hray, hdegree⟩ :=
    exists_artinSchreier_bounded_extension k K p m
  let N : Subgroup (IdeleClassGroup k K) :=
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range
  let J : Subgroup (IdeleClassGroup k K) :=
    IdeleGroup.primePowerJetClassSubgroup p (p • m) S
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hess : Algebra.EssFiniteType k K := essFiniteType k K
  have hplace : Nonempty (Place k K) := nonempty_place k K
  have hzero : FiniteDimensional k (LSpace (0 : Divisor k K)) :=
    finiteDimensional_lSpace_zero k K
  have hWfinite : Finite
      (boundedArtinSchreierClasses p (p • (AlgebraicCurve.Modulus.toDivisor m))) :=
    boundedArtinSchreierClasses_finite p (p • (AlgebraicCurve.Modulus.toDivisor m))
  have hJfinite : J.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by
    rw [hindex]
    exact Nat.card_pos.ne')
  have hpowers : (powMonoidHom (α := IdeleClassGroup k K) p).range ≤ N := by
    rintro c ⟨d, rfl⟩
    apply (abelianFiniteArtin_eq_one_iff_mem_norm k K E (d ^ p)).mp
    rw [map_pow]
    exact hexp (abelianFiniteArtin k K E d)
  have hmod : m₀ ≤ p • m := by
    intro v
    change m₀ v ≤ p * m v
    exact (hm v).trans (Nat.le_mul_of_pos_left (m v) (Fact.out : p.Prime).pos)
  have hsuppp : (p • m).support ⊆ S := Finsupp.support_smul.trans hsupp
  have hJray : J ≤ RayClass.powerRaySubgroup (p • m) p :=
    IdeleGroup.primePowerJetClassSubgroup_le_powerRaySubgroup p (p • m) S hsuppp
  have hJN : J ≤ N := hJray.trans (sup_le hray hpowers)
  have hbound : J.index ≤ N.index := by
    rw [hindex, finiteAbelian_norm_index k K E]
    exact hdegree
  have hEq : J = N := eq_of_le_of_not_lt hJN (fun hlt =>
    (not_lt_of_ge hbound) (Subgroup.index_strictAnti hlt))
  refine ⟨E, hfinite, hab, ?_⟩
  change N ≤ RayClass.powerRaySubgroup m₀ p
  rw [← hEq]
  exact hJray.trans (sup_le_sup_right (RayClass.rayClassSubgroup_antitone hmod) _)

end FunctionField
