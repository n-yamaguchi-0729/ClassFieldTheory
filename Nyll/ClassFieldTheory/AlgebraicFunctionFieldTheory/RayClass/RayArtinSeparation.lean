/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.RayPowerQuotient
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity

/-!
# Separation of actual ray classes by absolute reciprocity

The finite degree-zero subgroup and the integer degree imply that an element
of a ray class group divisible by every positive integer is the identity.
The existing finite ray-power quotients and actual finite norm cofinality
then show that absolute reciprocity detects membership in every ray subgroup.

Consequently the full ray class group embeds into the actual absolute abelian
Galois group modulo the Artin image of the ray congruence subgroup. No geometric
fundamental-group comparison is an input to this result.
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField.RayClass

open LocalClassFieldTheory

private theorem eq_one_of_all_positive_roots
    {G : Type*} [Group G] (f : G →* Multiplicative ℤ) [Finite f.ker]
    (x : G) (hx : ∀ n : ℕ, n ≠ 0 → ∃ y : G, y ^ n = x) : x = 1 := by
  have hdegree : (f x).toAdd = 0 := by
    by_contra hne
    let n : ℕ := (f x).toAdd.natAbs + 1
    obtain ⟨y, hy⟩ := hx n (Nat.succ_ne_zero _)
    have hmul : (n : ℤ) * (f y).toAdd = (f x).toAdd := by
      simpa only [map_pow, toAdd_pow, nsmul_eq_mul] using
        congrArg (fun z : G => (f z).toAdd) hy
    have hdvd : (n : ℤ) ∣ (f x).toAdd := ⟨(f y).toAdd, hmul.symm⟩
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne
    simp only [Int.natAbs_natCast] at hle
    change (f x).toAdd.natAbs + 1 ≤ (f x).toAdd.natAbs at hle
    omega
  let n : ℕ := Nat.card f.ker
  have hn : n ≠ 0 := Nat.card_pos.ne'
  obtain ⟨y, hy⟩ := hx n hn
  have hmul : (n : ℤ) * (f y).toAdd = 0 := by
    have h := congrArg (fun z : G => (f z).toAdd) hy
    simpa only [map_pow, toAdd_pow, nsmul_eq_mul, hdegree] using h
  have hydegree : (f y).toAdd = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (Int.natCast_ne_zero.mpr hn)
  have hyker : y ∈ f.ker := Multiplicative.ext hydegree
  have hcard : (⟨y, hyker⟩ : f.ker) ^ n = 1 := pow_card_eq_one'
  exact hy.symm.trans (congrArg Subtype.val hcard)

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The positive ray-power subgroups intersect in the original ray subgroup. -/
theorem mem_rayClassSubgroup_of_mem_all_powerRaySubgroups
    (m : Modulus k K) (c : IdeleClassGroup k K)
    (hc : ∀ n : ℕ, n ≠ 0 → c ∈ powerRaySubgroup m n) :
    c ∈ rayClassSubgroup m := by
  apply (QuotientGroup.eq_one_iff c).mp
  have : Finite (degree m).ker := finite_degreeZero m
  apply eq_one_of_all_positive_roots (degree m)
  intro n hn
  have hcn := hc n hn
  rw [powerRaySubgroup_eq_comap] at hcn
  exact hcn

/-- Actual finite norm cofinality forces the kernel of absolute reciprocity
into every actual ray subgroup. -/
theorem absoluteArtin_ker_le_rayClassSubgroup (m : Modulus k K) :
    (absoluteArtin k K).toMonoidHom.ker ≤ rayClassSubgroup m := by
  intro c hc
  apply mem_rayClassSubgroup_of_mem_all_powerRaySubgroups m c
  intro n hn
  let H : OpenFiniteIndexNormalSubgroup (IdeleClassGroup k K) :=
    ⟨{ toOpenSubgroup :=
        { toSubgroup := powerRaySubgroup m n
          isOpen' := isOpen_powerRaySubgroup m n }
       isNormal' := by
         refine ⟨?_⟩
         intro a ha b
         rw [mul_comm b a, mul_assoc, mul_inv_cancel, mul_one]
         exact ha }, finiteIndex_powerRaySubgroup m hn⟩
  obtain ⟨N, hNH⟩ := absoluteArtin_preimage_cofinal k K H
  apply hNH
  change absoluteArtin k K c ∈ N
  change absoluteArtin k K c = 1 at hc
  rw [hc]
  exact N.one_mem

/-- The actual Artin image of the ray congruence subgroup. -/
def artinRaySubgroup (m : Modulus k K) : Subgroup (localAbsoluteAbelianProfinite K) :=
  (rayClassSubgroup m).map (absoluteArtin k K).toMonoidHom

instance artinRaySubgroup_normal (m : Modulus k K) : (artinRaySubgroup m).Normal := by
  have : IsMulCommutative (localAbsoluteAbelianProfinite K) := by
    change IsMulCommutative (TopologicalAbelianization (intrinsicAbsoluteGalois K))
    infer_instance
  infer_instance

/-- This Artin image is compact, with its actual Krull quotient topology. -/
theorem isCompact_artinRaySubgroup (m : Modulus k K) :
    IsCompact (artinRaySubgroup m : Set (localAbsoluteAbelianProfinite K)) :=
  (isCompact_rayClassSubgroup m).image (absoluteArtin k K).continuous_toFun

/-- The actual ray Artin subgroup is closed, so its quotient is Hausdorff. -/
theorem isClosed_artinRaySubgroup (m : Modulus k K) :
    IsClosed (artinRaySubgroup m : Set (localAbsoluteAbelianProfinite K)) :=
  (isCompact_artinRaySubgroup m).isClosed

/-- Pulling the actual Artin image back gives precisely the original ray subgroup. -/
theorem artinRaySubgroup_comap_absoluteArtin (m : Modulus k K) :
    (artinRaySubgroup m).comap (absoluteArtin k K).toMonoidHom = rayClassSubgroup m :=
  Subgroup.comap_map_eq_self (absoluteArtin_ker_le_rayClassSubgroup m)

/-- The full actual ray class group maps to the corresponding absolute
abelian Galois quotient through the original absolute Artin homomorphism. -/
def rayClassAbsoluteArtin (m : Modulus k K) :
    RayClassGroup m →* localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
  QuotientGroup.lift (rayClassSubgroup m)
    ((QuotientGroup.mk' (artinRaySubgroup m)).comp (absoluteArtin k K).toMonoidHom)
    (fun c hc => (QuotientGroup.eq_one_iff _).mpr ⟨c, hc, rfl⟩)

/-- The ray-level map retains the original Artin value of every idele class. -/
theorem rayClassAbsoluteArtin_mk (m : Modulus k K) (c : IdeleClassGroup k K) :
    rayClassAbsoluteArtin m (QuotientGroup.mk' (rayClassSubgroup m) c) =
      QuotientGroup.mk' (artinRaySubgroup m) (absoluteArtin k K c) := rfl

/-- Absolute reciprocity separates all full ray classes, including the degree direction. -/
theorem rayClassAbsoluteArtin_injective (m : Modulus k K) :
    Function.Injective (rayClassAbsoluteArtin m) := by
  apply (injective_iff_map_eq_one (rayClassAbsoluteArtin m)).mpr
  intro r hr
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (rayClassSubgroup m) r
  apply (QuotientGroup.eq_one_iff c).mpr
  have hr' : QuotientGroup.mk' (artinRaySubgroup m) (absoluteArtin k K c) = 1 := hr
  have hc : c ∈ (artinRaySubgroup m).comap (absoluteArtin k K).toMonoidHom :=
    (QuotientGroup.eq_one_iff (absoluteArtin k K c)).mp hr'
  rw [artinRaySubgroup_comap_absoluteArtin] at hc
  exact hc

end FunctionField.RayClass
