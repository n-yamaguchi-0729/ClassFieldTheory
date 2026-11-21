/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Mathlib.Data.Finsupp.Order
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Projection between ideal-theoretic ray class groups

Enlarging a modulus strengthens its finite congruences and real positivity
conditions. The induced inclusions of prime-to-modulus ideals and ray-principal
ideals give the canonical quotient map from the larger modulus to the smaller.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- Enlarging the modulus shrinks the subgroup of ideals prime to it. -/
theorem rayPrimeToIdeals_antitone
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    rayClassPrimeToIdeals n ≤ rayClassPrimeToIdeals m := by
  intro I hI v hv
  exact hI v (Finsupp.support_mono hmn.1 hv)

/-- Enlarging the modulus shrinks the ray principal ideal subgroup. -/
theorem rayPrincipalIdeals_antitone
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    rayPrincipalIdealSubgroup n ≤ rayPrincipalIdealSubgroup m := by
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, hIx⟩
  exact ⟨x, IsRayCongruent.of_le hmn hx, hIx⟩

/-- The ideal-theoretic ray class group modulo a larger modulus projects to
the ray class group modulo a smaller modulus. -/
def rayClassIdealModulusProjection
    (K : Type u) [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    RayClassGroup n →* RayClassGroup m := by
  let hI : rayClassPrimeToIdeals n ≤ rayClassPrimeToIdeals m :=
    rayPrimeToIdeals_antitone hmn
  letI : (rayPrincipalIdealSubgroupInPrimeTo m).Normal :=
    Subgroup.normal_of_isMulCommutative _
  refine QuotientGroup.map
    (rayPrincipalIdealSubgroupInPrimeTo n)
    (rayPrincipalIdealSubgroupInPrimeTo m)
    (Subgroup.inclusion hI) ?_
  intro I hI'
  change (I : NumberFieldFractionalIdealGroup K) ∈
    rayPrincipalIdealSubgroup n at hI'
  change (I : NumberFieldFractionalIdealGroup K) ∈
    rayPrincipalIdealSubgroup m
  exact rayPrincipalIdeals_antitone hmn hI'

/-- Reduction along the identity modulus is the identity on the original
ideal-theoretic ray class group. -/
theorem rayClassIdealModulusProjection_refl
    (K : Type u) [Field K] [NumberField K] (m : RayClassModulus K) :
    rayClassIdealModulusProjection K (le_refl m) = MonoidHom.id (RayClassGroup m) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) x
  rfl

/-- Successive reductions retain the same original ideal representative. -/
theorem rayClassIdealModulusProjection_trans
    (K : Type u) [Field K] [NumberField K]
    {m n p : RayClassModulus K} (hmn : m ≤ n) (hnp : n ≤ p) :
    (rayClassIdealModulusProjection K hmn).comp (rayClassIdealModulusProjection K hnp) =
      rayClassIdealModulusProjection K (hmn.trans hnp) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo p) x
  rfl

end ClassFieldTheory
