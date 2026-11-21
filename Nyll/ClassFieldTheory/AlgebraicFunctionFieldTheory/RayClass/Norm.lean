/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegBifiber
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteNormProperties
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Degree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.NormCongruence
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange

/-!
# The norm on full function-field ray class groups

For a finite extension, the original idele norm sends congruence ideles for the
divisor pullback into congruence ideles for the base modulus. The resulting norm
descends from the actual finite idele class norm and preserves degree.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.RayClass

section FiniteExtension

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L]

private theorem localNormOver_mem_higherUnit
    (m : Modulus k K) (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (x : w.adicCompletionˣ) (hx : x ∈ localHigherUnitGroup w (pullbackDivisor L m w)) :
    IdeleGroup.localNormOver v w hw x ∈ localHigherUnitGroup v (m v) := by
  subst v
  rw [pullbackDivisor_apply] at hx
  exact localNorm_mem_higherUnit w (m (w.restrict K)) x hx

/-- The actual idele norm preserves the divisor-pullback ray congruences.
Each factor in the norm at a base place lies in the same base higher-unit group. -/
theorem norm_mem_congruenceSubgroup (m : Modulus k K) (a : IdeleGroup k L)
    (ha : a ∈ congruenceSubgroup (pullbackDivisor L m)) :
    IdeleGroup.norm (K := K) a ∈ congruenceSubgroup m := by
  intro v
  change IdeleGroup.normComponent (K := K) (L := L) v a ∈ localHigherUnitGroup v (m v)
  rw [IdeleGroup.normComponent_apply]
  apply Subgroup.prod_mem
  intro w _
  exact localNormOver_mem_higherUnit m v w.val
    ((Place.mem_fiberOver v).mp w.property) (a w.val) (ha w.val)

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The original class norm maps the image of the upstairs congruence subgroup
into the downstairs ray subgroup. -/
theorem finiteNorm_mem_rayClassSubgroup (m : Modulus k K) {c : IdeleClassGroup k L}
    (hc : c ∈ rayClassSubgroup (pullbackDivisor L m)) :
    IdeleClassGroup.finiteNorm (K := K) c ∈ rayClassSubgroup m := by
  obtain ⟨a, ha, rfl⟩ := hc
  exact ⟨IdeleGroup.norm (K := K) a, norm_mem_congruenceSubgroup m a ha,
    (IdeleClassGroup.finiteNorm_mk (K := K) a).symm⟩

/-- The norm on the full ray class quotient for the ramification-weighted
pullback modulus. It is induced by the original idele class norm. -/
def rayNorm (m : Modulus k K) : RayClassGroup (pullbackDivisor L m) →* RayClassGroup m :=
  QuotientGroup.map (rayClassSubgroup (pullbackDivisor L m)) (rayClassSubgroup m)
    (IdeleClassGroup.finiteNorm (K := K) (L := L))
    (fun _ hc => finiteNorm_mem_rayClassSubgroup m hc)

@[simp]
theorem rayNorm_mk (m : Modulus k K) (c : IdeleClassGroup k L) :
    rayNorm (L := L) m (QuotientGroup.mk' (rayClassSubgroup (pullbackDivisor L m)) c) =
      QuotientGroup.mk' (rayClassSubgroup m) (IdeleClassGroup.finiteNorm (K := K) c) :=
  rfl

@[simp]
theorem rayNorm_mk_idele (m : Modulus k K) (a : IdeleGroup k L) :
    rayNorm (L := L) m
        (QuotientGroup.mk' (rayClassSubgroup (pullbackDivisor L m)) (IdeleClassGroup.mk a)) =
      QuotientGroup.mk' (rayClassSubgroup m) (IdeleClassGroup.mk (IdeleGroup.norm (K := K) a)) :=
  (rayNorm_mk m (IdeleClassGroup.mk a)).trans
    (congrArg (QuotientGroup.mk' (rayClassSubgroup m))
      (IdeleClassGroup.finiteNorm_mk (K := K) a))

/-- The full ray norm is continuous for the quotient topologies. -/
theorem continuous_rayNorm (m : Modulus k K) : Continuous (rayNorm (L := L) m) := by
  apply (QuotientGroup.isQuotientMap_mk
    (rayClassSubgroup (pullbackDivisor L m))).continuous_iff.mpr
  change Continuous ((QuotientGroup.mk' (rayClassSubgroup m)) ∘
    (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)))
  exact QuotientGroup.continuous_mk.comp IdeleClassGroup.continuous_finiteNorm

/-- The full ray norm preserves the original degree of the idele class. -/
@[simp]
theorem degree_rayNorm (m : Modulus k K) (c : RayClassGroup (pullbackDivisor L m)) :
    degree m (rayNorm (L := L) m c) = degree (pullbackDivisor L m) c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (rayClassSubgroup (pullbackDivisor L m)) c
  rw [rayNorm_mk, degree_mk, degree_mk, IdeleClassGroup.degree_finiteNorm]

end FiniteExtension

private theorem rayClassCast_mk
    {k K : Type*} [Field k] [Field K] [Algebra k K] [HasPrincipalDivisors k K]
    {m n : Modulus k K} (h : m = n) (a : IdeleClassGroup k K) :
    MulEquiv.cast (M := RayClassGroup) h (QuotientGroup.mk' (rayClassSubgroup m) a) =
      QuotientGroup.mk' (rayClassSubgroup n) a := by
  subst n
  rfl

section Tower

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k L M] [IsScalarTower k K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

/-- Pulling back divisor multiplicities through a tower gives the direct pullback. -/
theorem pullbackDivisor_trans (m : Modulus k K) :
    pullbackDivisor M (pullbackDivisor L m) = pullbackDivisor M m := by
  apply Finsupp.ext
  intro w
  have hplace : (w.restrict L).restrict K = w.restrict K :=
    restrict_restrict (F := K) (E := L) w
  have he : w.ramificationIndex K = w.ramificationIndex L *
      (w.restrict L).ramificationIndex K :=
    Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := K) (E := L) w
  rw [pullbackDivisor_apply (pullbackDivisor L m) w, pullbackDivisor_apply m (w.restrict L),
    pullbackDivisor_apply m w, hplace, ← mul_assoc, ← he]

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- The full ray class norms compose after identifying the two pullback moduli. -/
theorem rayNorm_trans (m : Modulus k K)
    (c : RayClassGroup (pullbackDivisor M (pullbackDivisor L m))) :
    rayNorm (L := L) m (rayNorm (L := M) (pullbackDivisor L m) c) =
      rayNorm (L := M) m
        (MulEquiv.cast (M := RayClassGroup) (pullbackDivisor_trans (L := L) (M := M) m) c) := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective (rayClassSubgroup (pullbackDivisor M (pullbackDivisor L m))) c
  rw [rayNorm_mk, rayNorm_mk, rayClassCast_mk, rayNorm_mk]
  exact congrArg (QuotientGroup.mk' (rayClassSubgroup m))
    (IdeleClassGroup.finiteNorm_trans (k := k) (K := K) (L := L) (M := M) a)

end Tower

end FunctionField.RayClass
