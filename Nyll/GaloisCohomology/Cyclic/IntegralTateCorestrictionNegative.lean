/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransfer
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNegativeBoundaries

/-!
# The original representatives under negative corestriction

The degree-zero coset norm and the induction-shift boundary identify
corestriction on norm-zero vectors. The preceding bar boundary then
identifies degree-minus-two corestriction with abelianized inclusion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype H] in
private theorem relativeNorm_map {A B : Rep.{u} ℤ G} (f : A ⟶ B) (a : A) :
    f (relativeNorm H A a) = relativeNorm H B (f a) := by
  simp only [relativeNorm, LinearMap.sum_apply, map_sum, Rep.hom_comm_apply]

/-- Corestriction in degree minus one keeps the original norm-zero vector. -/
theorem tateCorestrict_negOneNormClass (A : Rep.{u} ℤ G) (a : A)
    (h : (Rep.res H.subtype A).ρ.norm a = 0) :
    tateCorestrict H A (-1) (tateNegOneNormClass (Rep.res H.subtype A) a h) =
      tateNegOneNormClass A a (by rw [← relativeNorm_subgroupNorm H A a, h, map_zero]) := by
  let S := Rep.indShiftSequence A
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let T := S.map F
  let hS := Rep.indShiftSequence_shortExact A
  let hT := subgroupRestrict_shortExact H hS
  let b : S.X₂ := Rep.indShiftSection A a
  let bH : T.X₂ := b
  have hb : S.g b = a := Rep.indShiftCounit_section A a
  have he : T.g (T.X₂.ρ.norm bH) = 0 := by
    have hc := congrArg (fun f : T.X₂ ⟶ T.X₃ => f bH) (Rep.norm_comm T.g)
    change T.X₃.ρ.norm (T.g bH) = T.g (T.X₂.ρ.norm bH) at hc
    have hz : T.X₃.ρ.norm (T.g bH) = 0 := by
      change (Rep.res H.subtype A).ρ.norm (S.g b) = 0
      rw [hb]
      exact h
    exact hc.symm.trans hz
  let K := forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ)
  obtain ⟨x₀, hx₀⟩ := (ShortComplex.moduleCat_exact_iff (T.map K)).mp
    (hT.map_of_exact K).exact (T.X₂.ρ.norm bH) he
  let x : T.X₁ := x₀
  have hx : T.f x = T.X₂.ρ.norm bH := hx₀
  let X : T.X₁.ρ.invariants := ⟨x, fun g => by
    apply (Rep.mono_iff_injective T.f).mp hT.mono_f
    change T.f (T.X₁.ρ g x) = T.f x
    rw [Rep.hom_comm_apply, hx]
    exact T.X₂.ρ.self_norm_apply g bH⟩
  let Y := corestrictInvariants H S.X₁ X
  have hY : S.f Y.val = S.X₂.ρ.norm b := by
    change S.f (relativeNorm H S.X₁ x) = S.X₂.ρ.norm b
    rw [relativeNorm_map H S.f, show S.f x = T.X₂.ρ.norm bH from hx]
    exact relativeNorm_subgroupNorm H S.X₂ b
  have hA : A.ρ.norm a = 0 := by rw [← relativeNorm_subgroupNorm H A a, h, map_zero]
  have h₁ := tateδ_negOneNormClass hT a h bH hb X hx
  have h₂ := tateδ_negOneNormClass hS a hA b hb Y hY
  apply (indShiftDownEquiv A (-1)).injective
  refine (tateCorestrict_indShift H A 0 (tateNegOneNormClass T.X₃ a h)).trans ?_
  change tateCorestrict H S.X₁ 0 (tateδ hT (-1) (tateNegOneNormClass T.X₃ a h)) =
    tateδ hS (-1) (tateNegOneNormClass S.X₃ a hA)
  rw [h₁, h₂]
  exact tateCorestrict_zero_fixedClass H S.X₁ X

/-- Corestriction takes the original subgroup bar class to the same bar chain
read in the whole group. -/
theorem tateCorestrict_negTwoBarClass (A : Rep.{u} ℤ G) (h : H) (a : A)
    (ha : A.ρ (h : G)⁻¹ a = a) :
    tateCorestrict H A (-2) (tateNegTwoBarClass (Rep.res H.subtype A) h a ha) =
      tateNegTwoBarClass A h.val a ha := by
  let S := Rep.indShiftSequence A
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let T := S.map F
  let hS := Rep.indShiftSequence_shortExact A
  let hT := subgroupRestrict_shortExact H hS
  let b : S.X₂ := Rep.indShiftSection A a
  let bH : T.X₂ := b
  have hb : S.g b = a := Rep.indShiftCounit_section A a
  let y : S.X₂ := S.X₂.ρ (h : G)⁻¹ b - b
  have hy : S.g y = 0 := by
    change S.g (S.X₂.ρ (h : G)⁻¹ b - b) = 0
    rw [map_sub, Rep.hom_comm_apply, hb]
    change A.ρ (h : G)⁻¹ a - a = 0
    exact sub_eq_zero.mpr ha
  let K := forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ)
  obtain ⟨x₀, hx₀⟩ := (ShortComplex.moduleCat_exact_iff (S.map K)).mp
    (hS.map_of_exact K).exact y hy
  let x : S.X₁ := x₀
  let xH : T.X₁ := x
  have hx : S.f x = y := hx₀
  have hnorm : T.X₁.ρ.norm xH = 0 := by
    apply (Rep.mono_iff_injective T.f).mp hT.mono_f
    have hh := congrArg (fun f : T.X₁ ⟶ T.X₂ => f xH) (Rep.norm_comm T.f)
    change T.X₂.ρ.norm (T.f xH) = T.f (T.X₁.ρ.norm xH) at hh
    rw [← hh, map_zero]
    change T.X₂.ρ.norm (S.f x) = 0
    rw [hx]
    change T.X₂.ρ.norm (T.X₂.ρ h⁻¹ bH - bH) = 0
    rw [map_sub, Representation.norm_self_apply, sub_self]
  have hnorm' : S.X₁.ρ.norm x = 0 := by
    have hres : (Rep.res H.subtype S.X₁).ρ.norm x = 0 := hnorm
    rw [← relativeNorm_subgroupNorm H S.X₁ x, hres, map_zero]
  have h₁ := tateδ_negTwoBarClass hT h a ha bH hb xH hx hnorm
  have h₂ := tateδ_negTwoBarClass hS h.val a ha b hb x hx hnorm'
  apply (indShiftDownEquiv A (-2)).injective
  refine (tateCorestrict_indShift H A 1 (tateNegTwoBarClass T.X₃ h a ha)).trans ?_
  change tateCorestrict H S.X₁ (-1) (tateδ hT (-2) (tateNegTwoBarClass T.X₃ h a ha)) =
    tateδ hS (-2) (tateNegTwoBarClass S.X₃ h.val a ha)
  rw [h₁, h₂]
  exact tateCorestrict_negOneNormClass H S.X₁ x hnorm

/-- The integral bar generator is sent to the same group element by corestriction. -/
theorem tateCorestrict_negTwoUnitClass (h : H) :
    tateCorestrict H (integralTrivialInteger.{u, u} G) (-2) (tateNegTwoUnitClass H h) =
      tateNegTwoUnitClass G h.val := by
  rw [tateNegTwoUnitClass_eq_bar, tateNegTwoUnitClass_eq_bar]
  exact tateCorestrict_negTwoBarClass H (integralTrivialInteger G) h
    (integralTrivialIntegerOne G) rfl

/-- The degree-minus-two corestriction is the original map on abelianizations
induced by the subgroup inclusion. -/
theorem tateCorestrict_negTwo_abelianization (x : tate (integralTrivialInteger.{u, u} H) (-2)) :
    tateNegTwoUnitAbelianizationEquiv G (tateCorestrict H (integralTrivialInteger G) (-2) x) =
      Additive.ofMul (Group.Abelianization.map H.subtype
        (Additive.toMul (tateNegTwoUnitAbelianizationEquiv H x))) := by
  let e := tateNegTwoUnitAbelianizationEquiv.{u, u} H
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (Additive.toMul (e x))
  have hx : tateNegTwoUnitClass H h = x := by
    apply e.injective
    change tateNegTwoUnitAbelianizationEquiv H (tateNegTwoUnitClass H h) = e x
    rw [tateNegTwoUnitAbelianizationEquiv_class]
    exact congrArg Additive.ofMul hh
  rw [← hx, tateCorestrict_negTwoUnitClass, tateNegTwoUnitAbelianizationEquiv_class,
    tateNegTwoUnitAbelianizationEquiv_class]
  rfl

end IntegralGroupCohomology.Universe
