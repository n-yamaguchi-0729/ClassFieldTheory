/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateDimensionShiftNaturality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransfer
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInducedShiftNaturality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorNorm

/-!
# Naturality of the integral Tate group transfer maps

The group transfer maps respect coefficient morphisms in all degrees.
In particular, subgroup restriction commutes with cup product by a
degree-zero class in every left degree.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

/-- The subgroup restriction commutes with the original coefficient maps in every degree. -/
theorem tateRestrict_naturality (n : ℤ) : ∀ {A B : Rep.{u} ℤ G}
    (f : A ⟶ B) (x : tate A n),
    (tateFunctor H n).map ((Rep.resFunctor H.subtype).map f) (tateRestrict H A n x) =
      tateRestrict H B n ((tateFunctor G n).map f x) := by
  cases n with
  | ofNat i =>
    induction i with
    | zero =>
      intro A B f x
      exact tateZeroRestrict_naturality H f x
    | succ i ih =>
      intro A B f x
      obtain ⟨z, rfl⟩ := (coindShiftUpEquiv A i).surjective x
      change (tateFunctor H (↑(i + 1) : ℤ)).map ((Rep.resFunctor H.subtype).map f)
          (tateRestrict H A (↑(i + 1) : ℤ) (coindShiftUpEquiv A i z)) =
        tateRestrict H B (↑(i + 1) : ℤ)
          ((tateFunctor G (↑(i + 1) : ℤ)).map f (coindShiftUpEquiv A i z))
      let p := (tateFunctor H (↑(i + 1) : ℤ)).map ((Rep.resFunctor H.subtype).map f)
      let f' := Rep.coindShiftUpMap f
      let z' := (tateFunctor G (i : ℤ)).map f' z
      calc
        _ = p (subgroupCoindShiftEquiv H A i (tateRestrict H (Rep.coindShiftUp A) i z)) :=
          congrArg p (tateRestrict_coindShift H A i z)
        _ = _ := subgroupCoindShiftEquiv_naturality H f (i : ℤ)
          (tateRestrict H (Rep.coindShiftUp A) i z)
        _ = subgroupCoindShiftEquiv H B i (tateRestrict H (Rep.coindShiftUp B) i z') :=
          congrArg (subgroupCoindShiftEquiv H B i) (ih f' z)
        _ = tateRestrict H B (↑(i + 1) : ℤ) (coindShiftUpEquiv B i z') :=
          (tateRestrict_coindShift H B i z').symm
        _ = _ := congrArg (tateRestrict H B (↑(i + 1) : ℤ))
          (coindShiftUpEquiv_naturality_apply f (i : ℤ) z).symm
  | negSucc i =>
    induction i with
    | zero =>
      intro A B f x
      apply (subgroupIndShiftEquiv H B (Int.negSucc 0)).injective
      rw [← subgroupIndShiftEquiv_naturality H f (Int.negSucc 0),
        tateRestrict_indShift H A 0, tateRestrict_indShift H B 0,
        ← indShiftDownEquiv_naturality_apply f (Int.negSucc 0)]
      exact tateZeroRestrict_naturality H _ _
    | succ i ih =>
      intro A B f x
      apply (subgroupIndShiftEquiv H B (Int.negSucc (i + 1))).injective
      rw [← subgroupIndShiftEquiv_naturality H f (Int.negSucc (i + 1)),
        tateRestrict_indShift H A (i + 1), tateRestrict_indShift H B (i + 1),
        ← indShiftDownEquiv_naturality_apply f (Int.negSucc (i + 1))]
      exact ih _ _

/-- The subgroup corestriction commutes with the original coefficient maps in every degree. -/
theorem tateCorestrict_naturality (n : ℤ) : ∀ {A B : Rep.{u} ℤ G}
    (f : A ⟶ B) (x : tate (Rep.res H.subtype A) n),
    (tateFunctor G n).map f (tateCorestrict H A n x) =
      tateCorestrict H B n ((tateFunctor H n).map ((Rep.resFunctor H.subtype).map f) x) := by
  cases n with
  | ofNat i =>
    induction i with
    | zero =>
      intro A B f x
      exact tateZeroCorestrict_naturality H f x
    | succ i ih =>
      intro A B f x
      obtain ⟨z, rfl⟩ := (subgroupCoindShiftEquiv H A i).surjective x
      change (tateFunctor G (↑(i + 1) : ℤ)).map f
          (tateCorestrict H A (↑(i + 1) : ℤ) (subgroupCoindShiftEquiv H A i z)) =
        tateCorestrict H B (↑(i + 1) : ℤ)
          ((tateFunctor H (↑(i + 1) : ℤ)).map ((Rep.resFunctor H.subtype).map f)
            (subgroupCoindShiftEquiv H A i z))
      let p := (tateFunctor G (↑(i + 1) : ℤ)).map f
      let f' := Rep.coindShiftUpMap f
      let z' := (tateFunctor H (i : ℤ)).map ((Rep.resFunctor H.subtype).map f') z
      calc
        _ = p (coindShiftUpEquiv A i (tateCorestrict H (Rep.coindShiftUp A) i z)) :=
          congrArg p (tateCorestrict_coindShift H A i z)
        _ = _ := coindShiftUpEquiv_naturality_apply f (i : ℤ)
          (tateCorestrict H (Rep.coindShiftUp A) i z)
        _ = coindShiftUpEquiv B i (tateCorestrict H (Rep.coindShiftUp B) i z') :=
          congrArg (coindShiftUpEquiv B i) (ih f' z)
        _ = tateCorestrict H B (↑(i + 1) : ℤ) (subgroupCoindShiftEquiv H B i z') :=
          (tateCorestrict_coindShift H B i z').symm
        _ = _ := congrArg (tateCorestrict H B (↑(i + 1) : ℤ))
          (subgroupCoindShiftEquiv_naturality H f (i : ℤ) z).symm
  | negSucc i =>
    induction i with
    | zero =>
      intro A B f x
      apply (indShiftDownEquiv B (Int.negSucc 0)).injective
      rw [← indShiftDownEquiv_naturality_apply f (Int.negSucc 0),
        tateCorestrict_indShift H A 0, tateCorestrict_indShift H B 0,
        ← subgroupIndShiftEquiv_naturality H f (Int.negSucc 0)]
      exact tateZeroCorestrict_naturality H _ _
    | succ i ih =>
      intro A B f x
      apply (indShiftDownEquiv B (Int.negSucc (i + 1))).injective
      rw [← indShiftDownEquiv_naturality_apply f (Int.negSucc (i + 1)),
        tateCorestrict_indShift H A (i + 1), tateCorestrict_indShift H B (i + 1),
        ← subgroupIndShiftEquiv_naturality H f (Int.negSucc (i + 1))]
      exact ih _ _

/-- Restriction and cup product by a degree-zero class commute in every left degree. -/
theorem tateRestrict_tensorCupZeroRight (A B : Rep.{u} ℤ G) (n : ℤ)
    (x : tate A n) (y : tate B 0) :
    tateRestrict H (A ⊗ᵣ B) n (tensorCupZeroRight A B n x y) =
      tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) n
        (tateRestrict H A n x) (tateRestrict H B 0 y) := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective B y
  rw [tensorCupZeroRight_fixedClass, tateRestrict_zero_fixedClass,
    tensorCupZeroRight_fixedClass, ← tateRestrict_naturality]
  rfl

end IntegralGroupCohomology.Universe
