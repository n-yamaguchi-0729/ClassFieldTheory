/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransfer
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation

/-!
# Positive Tate restriction is the original ordinary restriction

Both maps preserve the upward connecting sequence. At the transition from
degree zero to degree one they use the same invariant representative before
taking its class and applying the actual boundary.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
  [Fintype H] [Fintype (G ⧸ H)]

/-- The all-degree Tate restriction in a successor degree is the pullback
of ordinary cochains along the original subgroup inclusion. -/
theorem tateRestrict_succ_eq_positiveMapAlong (n : ℕ) (A : Rep.{u} ℤ G)
    (x : tate A (n + 1 : ℕ)) :
    tateRestrict H A (n + 1 : ℕ) x =
      tatePositiveMapAlong H.subtype (𝟙 (Rep.res H.subtype A)) (n + 1) x := by
  induction n generalizing A with
  | zero =>
    obtain ⟨z, rfl⟩ := (coindShiftUpEquiv A 0).surjective x
    obtain ⟨a, rfl⟩ := fixedClass_surjective (Rep.coindShiftUp A) z
    let S := Rep.coindShiftSequence A
    let hS := Rep.coindShiftSequence_shortExact A
    let S' := S.map (Rep.resFunctor H.subtype)
    have hd := tatePositiveMapAlong_δ_fixedClass H.subtype hS
      (subgroupRestrict_shortExact H hS) (𝟙 S') a
    change tatePositiveMapAlong H.subtype (𝟙 (Rep.res H.subtype A)) 1
        (coindShiftUpEquiv A 0 (fixedClass (Rep.coindShiftUp A) a)) =
      subgroupCoindShiftEquiv H A 0 (fixedClass (Rep.res H.subtype (Rep.coindShiftUp A))
        (restrictInvariants H (Rep.coindShiftUp A) a)) at hd
    let z := fixedClass (Rep.coindShiftUp A) a
    have h₀ := tateRestrict_coindShift H A 0 z
    have hz := tateRestrict_zero_fixedClass H (Rep.coindShiftUp A) a
    exact h₀.trans ((congrArg (subgroupCoindShiftEquiv H A 0) hz).trans hd.symm)
  | succ n ih =>
    obtain ⟨z, rfl⟩ := (coindShiftUpEquiv A (n + 1 : ℕ)).surjective x
    let S := Rep.coindShiftSequence A
    let hS := Rep.coindShiftSequence_shortExact A
    let S' := S.map (Rep.resFunctor H.subtype)
    have hd := congrArg (fun m : tate (Rep.coindShiftUp A) (n + 1 : ℕ) ⟶
        tate (Rep.res H.subtype A) (n + 1 + 1 : ℕ) => m z)
      (tatePositiveMapAlong_δ H.subtype hS (subgroupRestrict_shortExact H hS) (𝟙 S') (n + 1))
    change tatePositiveMapAlong H.subtype (𝟙 (Rep.res H.subtype A)) (n + 1 + 1)
        (coindShiftUpEquiv A (n + 1 : ℕ) z) =
      subgroupCoindShiftEquiv H A (n + 1 : ℕ)
        (tatePositiveMapAlong H.subtype
          (𝟙 (Rep.res H.subtype (Rep.coindShiftUp A))) (n + 1) z) at hd
    rw [tateRestrict_coindShift, ih, hd]

/-- Under the actual positive comparison the all-degree subgroup restriction
is the literal group cohomology map on the original subgroup and coefficient. -/
theorem tateRestrict_positive_comparison (n : ℕ) [NeZero n]
    (A : Rep.{u} ℤ G) (x : tate A n) :
    (tatePositiveIsoCohomology (Rep.res H.subtype A) n).hom (tateRestrict H A n x) =
      cohomologyMapAlong H.subtype (𝟙 (Rep.res H.subtype A)) n
        ((tatePositiveIsoCohomology A n).hom x) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [tateRestrict_succ_eq_positiveMapAlong]
    exact congrArg
      (fun m : tate A (n + 1 : ℕ) ⟶ cohomology (Rep.res H.subtype A) (n + 1) => m x)
      (tatePositiveMapAlong_comp_comparison H.subtype (𝟙 (Rep.res H.subtype A)) (n + 1))

/-- The positive comparison with ordinary cohomology in the original acting
group's universe, with the original coefficient action over lifted integers. -/
def tatePositiveIsoCommonCohomology (A : Rep.{u} ℤ G) (n : ℕ) [NeZero n] :
    tate A n ≅ IntegralGroupCohomology.cohomology A n :=
  tatePositiveIsoCohomology A n ≪≫ cohomologyIsoCommon A n

/-- Subgroup restriction under the common comparison is ordinary restriction
with the literal subgroup inclusion and the unchanged coefficient. -/
theorem tateRestrict_positive_comp_common (n : ℕ) [NeZero n] (A : Rep.{u} ℤ G) (x : tate A n) :
    (tatePositiveIsoCommonCohomology (Rep.res H.subtype A) n).hom (tateRestrict H A n x) =
      groupCohomology.map H.subtype
        (𝟙 ((IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype A))) n
        ((tatePositiveIsoCommonCohomology A n).hom x) := by
  let F := IntegralGroupCohomology.coefficientFunctor H
  let R := Rep.res H.subtype A
  let y := (tatePositiveIsoCohomology A n).hom x
  have h₁ := congrArg (cohomologyIsoCommon R n).hom
    (tateRestrict_positive_comparison H n A x)
  have h₂ := ConcreteCategory.congr_hom
    (cohomologyMapAlong_comp_common H.subtype (𝟙 R) n) y
  have hF : F.map (𝟙 R) = 𝟙 (F.obj R) := F.map_id R
  let J := IntegralGroupCohomology.integerScalars.{u}
  let a := (tatePositiveIsoCommonCohomology A n).hom x
  have h₃ := congrArg (fun m : F.obj R ⟶ F.obj R =>
    (J.map (groupCohomology.map H.subtype m n)) a) hF
  exact h₁.trans (h₂.trans h₃)

end IntegralGroupCohomology.Universe
