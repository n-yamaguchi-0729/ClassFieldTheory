/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Invariants
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNormCriterion
public import Nyll.GaloisCohomology.Cyclic.IntegralTateZeroTransfers

/-!
# Tate degree minus one and normal-subgroup norms

When the subgroup norm identifies coinvariants with invariants, transitivity
of the original finite norm reduces degree-minus-one vanishing to the quotient.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (T : Subgroup G) [T.Normal] [Fintype T]

/-- The actual subgroup norm with codomain the original subgroup invariants. -/
def normalSubgroupNorm (A : Rep.{v} ℤ G) :
    let B := A.quotientToInvariants T
    let : Module ℤ A := A.hV2
    let : Module ℤ B := B.hV2
    A →ₗ[ℤ] B := by
  intro B _ _
  let D := Rep.res T.subtype A
  exact D.ρ.norm.codRestrict D.ρ.invariants (fun x =>
    (Representation.mem_invariants D.ρ (D.ρ.norm x)).mpr (fun g => D.ρ.self_norm_apply g x))

omit [Fintype G] in
private theorem normalSubgroupNorm_val (A : Rep.{v} ℤ G) (x : A) :
    (normalSubgroupNorm T A x).val = (Rep.res T.subtype A).ρ.norm x := rfl

omit [Fintype G] [Fintype T] in
private theorem quotientToInvariants_apply_val (A : Rep.{v} ℤ G) (g : G)
    (x : A.quotientToInvariants T) :
    ((A.quotientToInvariants T).ρ (QuotientGroup.mk' T g) x).val = A.ρ g x.val := rfl

omit [Fintype G] in
/-- Normality makes the subgroup norm equivariant for the original action
and its quotient action on the invariants. -/
theorem normalSubgroupNorm_comm (A : Rep.{v} ℤ G) (g : G) (x : A) :
    normalSubgroupNorm T A (A.ρ g x) =
      (A.quotientToInvariants T).ρ (QuotientGroup.mk' T g) (normalSubgroupNorm T A x) := by
  apply Subtype.ext
  rw [normalSubgroupNorm_val, quotientToInvariants_apply_val, normalSubgroupNorm_val]
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  change (∑ t : T, A.ρ (t : G) (A.ρ g x)) = ∑ t : T, A.ρ g (A.ρ (t : G) x)
  simp only [← mul_apply_eq_comp, ← map_mul]
  let e : T ≃ T := (show MulAut T from MulAut.conjNormal g⁻¹).toEquiv
  refine Fintype.sum_equiv e _ _ (fun t => ?_)
  change A.ρ ((t : G) * g) x = A.ρ (g * (g⁻¹ * (t : G) * (g⁻¹)⁻¹)) x
  rw [inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

variable [Fintype (G ⧸ T)]

/-- The quotient norm after the actual subgroup norm is the original whole norm. -/
theorem quotientNorm_normalSubgroupNorm (A : Rep.{v} ℤ G) (x : A) :
    ((Rep.norm (A.quotientToInvariants T)).asHom.hom (normalSubgroupNorm T A x)).val =
      A.ρ.norm x := by
  let B := A.quotientToInvariants T
  let : Module ℤ B := B.hV2
  let y : B := normalSubgroupNorm T A x
  let D := (Rep.res T.subtype A).ρ.invariants
  change (B.ρ.norm y).val = _
  calc
    (B.ρ.norm y).val = (∑ q : G ⧸ T, B.ρ q y).val :=
      congrArg (fun z : B => z.val) (LinearMap.sum_apply Finset.univ B.ρ y)
    _ = ∑ q : G ⧸ T, (B.ρ q y).val :=
      Submodule.coe_sum (p := D) (fun q => B.ρ q y) Finset.univ
    _ = relativeNorm T A y.val := by
      rw [relativeNorm_apply]
      apply Finset.sum_congr rfl
      intro q _
      have hq : QuotientGroup.mk' T q.out = q := QuotientGroup.out_eq' q
      exact (congrArg (fun q => (B.ρ q y).val) hq.symm).trans
        (quotientToInvariants_apply_val T A q.out y)
    _ = A.ρ.norm x := (congrArg (relativeNorm T A) (normalSubgroupNorm_val T A x)).trans
      (relativeNorm_subgroupNorm T A x)

omit [Fintype G] [T.Normal] [Fintype T] [Fintype (G ⧸ T)] in
private theorem subgroupCoinvariants_le (A : Rep.{v} ℤ G) :
    Representation.Coinvariants.ker (Rep.res T.subtype A).ρ ≤
      Representation.Coinvariants.ker A.ρ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, x⟩, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker (ρ := A.ρ) (g : G) x

omit [Fintype G] [Fintype (G ⧸ T)] in
private theorem normalSubgroupNorm_map_coinvariants (A : Rep.{v} ℤ G)
    (hs : Function.Surjective (normalSubgroupNorm T A)) :
    let B := A.quotientToInvariants T
    let : Module ℤ A := A.hV2
    let : Module ℤ B := B.hV2
    (Representation.Coinvariants.ker A.ρ).map (normalSubgroupNorm T A) =
      Representation.Coinvariants.ker B.ρ := by
  intro B _ _
  let N := normalSubgroupNorm T A
  change (Representation.Coinvariants.ker A.ρ).map N = Representation.Coinvariants.ker B.ρ
  have hsub (g : G) (x : A) :
      N (A.ρ g x - x) = B.ρ (QuotientGroup.mk' T g) (N x) - N x :=
    (map_sub N (A.ρ g x) x).trans
      (congrArg (fun y : B => y - N x) (normalSubgroupNorm_comm T A g x))
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, x⟩, rfl⟩
    change N (A.ρ g x - x) ∈ Representation.Coinvariants.ker B.ρ
    rw [hsub]
    exact Representation.Coinvariants.sub_mem_ker (QuotientGroup.mk' T g) (N x)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨q, y⟩, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective T q
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨A.ρ g x - x, Representation.Coinvariants.sub_mem_ker g x, hsub g x⟩

/-- If degrees zero and minus one vanish on the normal subgroup, the
whole group's degree-minus-one vanishing is equivalent to that of the
actual quotient representation on the subgroup invariants. -/
theorem tateNegOne_quotient_isZero_iff (A : Rep.{v} ℤ G)
    (h₀ : IsZero (tate (Rep.res T.subtype A) 0))
    (h₁ : IsZero (tate (Rep.res T.subtype A) (-1))) :
    IsZero (tate (A.quotientToInvariants T) (-1)) ↔ IsZero (tate A (-1)) := by
  let B := A.quotientToInvariants T
  let : Module ℤ B := B.hV2
  let N := normalSubgroupNorm T A
  have hs : Function.Surjective N := by
    intro y
    obtain ⟨x, hx⟩ := (tateZero_isZero_iff_norm_surjective _).mp h₀ y
    exact ⟨x, Subtype.ext ((normalSubgroupNorm_val T A x).trans hx)⟩
  have hk := (tateNegOne_isZero_iff_norm_kernel _).mp h₁
  have hm := normalSubgroupNorm_map_coinvariants T A hs
  rw [tateNegOne_isZero_iff_norm_kernel, tateNegOne_isZero_iff_norm_kernel]
  constructor
  · intro h x hx
    have hz : B.ρ.norm (N x) = 0 := by
      apply Subtype.ext
      exact (quotientNorm_normalSubgroupNorm T A x).trans hx
    have hmem := h (N x) hz
    rw [← hm] at hmem
    obtain ⟨y, hy, hNy⟩ := hmem
    have hsub : (Rep.res T.subtype A).ρ.norm (x - y) = 0 := by
      have hzero : N (x - y) = 0 := by rw [map_sub, hNy, sub_self]
      exact (normalSubgroupNorm_val T A (x - y)).symm.trans (congrArg Subtype.val hzero)
    have hxsub := subgroupCoinvariants_le T A (hk (x - y) hsub)
    have hsum := (Representation.Coinvariants.ker A.ρ).add_mem hxsub hy
    rwa [sub_add_cancel] at hsum
  · intro h y hy
    obtain ⟨x, rfl⟩ := hs y
    have hz : A.ρ.norm x = 0 :=
      (quotientNorm_normalSubgroupNorm T A x).symm.trans (congrArg Subtype.val hy)
    rw [← hm]
    exact ⟨x, h x hz, rfl⟩

end IntegralGroupCohomology.Universe
