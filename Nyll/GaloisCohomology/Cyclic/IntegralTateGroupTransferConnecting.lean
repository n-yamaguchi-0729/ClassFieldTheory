/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransferNaturality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateSplitSequences

/-!
# Group transfer and the original Tate connecting maps

On a sequence split as ℤ-modules, the maps of short exact sequences to
coinduction and from induction extend the defining shift identities to
the actual connecting maps for that sequence and its restriction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

private theorem tateδ_naturality_apply {P : Type u} [Group P] [Fintype P]
    {S T : ShortComplex (Rep.{u} ℤ P)} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T) (n : ℤ) (x : tate S.X₃ n) :
    (tateFunctor P (n + 1)).map f.τ₁ (tateδ hS n x) =
      tateδ hT n ((tateFunctor P n).map f.τ₃ x) :=
  congrArg (fun g : tate S.X₃ n ⟶ tate T.X₁ (n + 1) => g x) (tateδ_naturality hS hT f n)

private theorem tate_map_endomorphism_apply_of_eq_id {P : Type u} [Group P] [Fintype P]
    {A : Rep.{u} ℤ P} {f : A ⟶ A} (hf : f = 𝟙 A) (n : ℤ) (x : tate A n) :
    (tateFunctor P n).map f x = x := by
  subst f
  exact congrArg (fun m : tate A n ⟶ tate A n => m x) ((tateFunctor P n).map_id A)

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

private theorem tateRestrict_mapped_indShift {A B : Rep.{u} ℤ G}
    (f : Rep.indShiftDown A ⟶ B) (i : ℕ) (x : tate A (Int.negSucc i)) :
    tateRestrict H B (Int.negSucc i + 1)
        ((tateFunctor G (Int.negSucc i + 1)).map f (indShiftDownEquiv A (Int.negSucc i) x)) =
      (tateFunctor H (Int.negSucc i + 1)).map ((Rep.resFunctor H.subtype).map f)
        (subgroupIndShiftEquiv H A (Int.negSucc i) (tateRestrict H A (Int.negSucc i) x)) := by
  let n := Int.negSucc i + 1
  let m := (tateFunctor H n).map ((Rep.resFunctor (k := ℤ) H.subtype).map f)
  exact (tateRestrict_naturality H n f (indShiftDownEquiv A (Int.negSucc i) x)).symm.trans
    (congrArg (fun y : tate (Rep.res H.subtype (Rep.indShiftDown A)) n => m y)
      (tateRestrict_indShift H A i x).symm)

private theorem tateCorestrict_mapped_indShift {A B : Rep.{u} ℤ G}
    (f : Rep.indShiftDown A ⟶ B) (i : ℕ) (x : tate (Rep.res H.subtype A) (Int.negSucc i)) :
    tateCorestrict H B (Int.negSucc i + 1)
        ((tateFunctor H (Int.negSucc i + 1)).map ((Rep.resFunctor H.subtype).map f)
          (subgroupIndShiftEquiv H A (Int.negSucc i) x)) =
      (tateFunctor G (Int.negSucc i + 1)).map f
        (indShiftDownEquiv A (Int.negSucc i) (tateCorestrict H A (Int.negSucc i) x)) := by
  let n := Int.negSucc i + 1
  let m := (tateFunctor G n).map f
  exact (tateCorestrict_naturality H n f (subgroupIndShiftEquiv H A (Int.negSucc i) x)).symm.trans
    (congrArg (fun y : tate (Rep.indShiftDown A) n => m y)
      (tateCorestrict_indShift H A i x).symm)

private theorem tateRestrict_connecting_neg {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (i : ℕ) (x : tate S.X₃ (Int.negSucc i)) :
    tateRestrict H S.X₁ ((Int.negSucc i) + 1) (tateδ hS (Int.negSucc i) x) =
      tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i)
        (tateRestrict H S.X₃ (Int.negSucc i) x) := by
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let f := compareFromIndShift hS split
  let fH := F.mapShortComplex.map f
  let hD := Rep.indShiftSequence_shortExact S.X₃
  have hf : f.τ₃ = 𝟙 S.X₃ := rfl
  have hfH : fH.τ₃ = 𝟙 (Rep.res H.subtype S.X₃) := F.map_id S.X₃
  have hG := tateδ_naturality_apply hD hS f (Int.negSucc i) x
  have hH := tateδ_naturality_apply (subgroupRestrict_shortExact H hD)
    (subgroupRestrict_shortExact H hS) fH (Int.negSucc i) (tateRestrict H S.X₃ (Int.negSucc i) x)
  have hG := hG.trans (congrArg (tateδ hS (Int.negSucc i))
    (tate_map_endomorphism_apply_of_eq_id hf (Int.negSucc i) x))
  have hH := hH.trans (congrArg (tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i))
    (tate_map_endomorphism_apply_of_eq_id hfH (Int.negSucc i)
      (tateRestrict H S.X₃ (Int.negSucc i) x)))
  change (tateFunctor G (Int.negSucc i + 1)).map f.τ₁ (indShiftDownEquiv S.X₃ (Int.negSucc i) x) =
    tateδ hS (Int.negSucc i) x at hG
  change (tateFunctor H (Int.negSucc i + 1)).map (F.map f.τ₁)
    (subgroupIndShiftEquiv H S.X₃ (Int.negSucc i) (tateRestrict H S.X₃ (Int.negSucc i) x)) =
      tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i)
        (tateRestrict H S.X₃ (Int.negSucc i) x) at hH
  calc
    _ = tateRestrict H S.X₁ (Int.negSucc i + 1)
        ((tateFunctor G (Int.negSucc i + 1)).map f.τ₁
          (indShiftDownEquiv S.X₃ (Int.negSucc i) x)) :=
      congrArg (tateRestrict H S.X₁ (Int.negSucc i + 1)) hG.symm
    _ = _ := by
      let a : Rep.indShiftDown S.X₃ ⟶ S.X₁ := f.τ₁
      exact (tateRestrict_mapped_indShift H a i x).trans hH

/-- Restriction commutes with the original connecting map of an underlying
split coefficient sequence in every integer degree. -/
theorem tateRestrict_connecting {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (n : ℤ) (x : tate S.X₃ n) :
    tateRestrict H S.X₁ (n + 1) (tateδ hS n x) =
      tateδ (subgroupRestrict_shortExact H hS) n (tateRestrict H S.X₃ n x) := by
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  cases n with
  | ofNat i =>
    let f := compareToCoindShift hS split
    let fH := F.mapShortComplex.map f
    let hD := Rep.coindShiftSequence_shortExact S.X₁
    have hf : f.τ₁ = 𝟙 S.X₁ := rfl
    have hfH : fH.τ₁ = 𝟙 (Rep.res H.subtype S.X₁) := F.map_id S.X₁
    have hG := tateδ_naturality_apply hS hD f i x
    have hH := tateδ_naturality_apply (subgroupRestrict_shortExact H hS)
      (subgroupRestrict_shortExact H hD) fH i (tateRestrict H S.X₃ i x)
    have hG := (tate_map_endomorphism_apply_of_eq_id hf ((i : ℤ) + 1) (tateδ hS i x)).symm.trans hG
    have hH := (tate_map_endomorphism_apply_of_eq_id hfH ((i : ℤ) + 1)
      (tateδ (subgroupRestrict_shortExact H hS) i (tateRestrict H S.X₃ i x))).symm.trans hH
    change tateδ hS i x = coindShiftUpEquiv S.X₁ i ((tateFunctor G i).map f.τ₃ x) at hG
    change tateδ (subgroupRestrict_shortExact H hS) i (tateRestrict H S.X₃ i x) =
      subgroupCoindShiftEquiv H S.X₁ i
        ((tateFunctor H i).map (F.map f.τ₃) (tateRestrict H S.X₃ i x)) at hH
    calc
      _ = tateRestrict H S.X₁ ((i : ℤ) + 1)
          (coindShiftUpEquiv S.X₁ i ((tateFunctor G i).map f.τ₃ x)) :=
        congrArg (tateRestrict H S.X₁ ((i : ℤ) + 1)) hG
      _ = _ := (tateRestrict_coindShift H S.X₁ i _).trans
        ((congrArg (subgroupCoindShiftEquiv H S.X₁ i)
          (tateRestrict_naturality H i f.τ₃ x).symm).trans hH.symm)
  | negSucc i => exact tateRestrict_connecting_neg H hS split i x

private theorem tateCorestrict_connecting_neg {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (i : ℕ) (x : tate (Rep.res H.subtype S.X₃) (Int.negSucc i)) :
    tateCorestrict H S.X₁ (Int.negSucc i + 1)
        (tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i) x) =
      tateδ hS (Int.negSucc i) (tateCorestrict H S.X₃ (Int.negSucc i) x) := by
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let f := compareFromIndShift hS split
  let fH := F.mapShortComplex.map f
  let hD := Rep.indShiftSequence_shortExact S.X₃
  have hf : f.τ₃ = 𝟙 S.X₃ := rfl
  have hfH : fH.τ₃ = 𝟙 (Rep.res H.subtype S.X₃) := F.map_id S.X₃
  have hG := tateδ_naturality_apply hD hS f (Int.negSucc i)
    (tateCorestrict H S.X₃ (Int.negSucc i) x)
  have hH := tateδ_naturality_apply (subgroupRestrict_shortExact H hD)
    (subgroupRestrict_shortExact H hS) fH (Int.negSucc i) x
  have hG := hG.trans (congrArg (tateδ hS (Int.negSucc i))
    (tate_map_endomorphism_apply_of_eq_id hf (Int.negSucc i)
      (tateCorestrict H S.X₃ (Int.negSucc i) x)))
  have hH := hH.trans (congrArg (tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i))
    (tate_map_endomorphism_apply_of_eq_id hfH (Int.negSucc i) x))
  change (tateFunctor G (Int.negSucc i + 1)).map f.τ₁
    (indShiftDownEquiv S.X₃ (Int.negSucc i) (tateCorestrict H S.X₃ (Int.negSucc i) x)) =
      tateδ hS (Int.negSucc i) (tateCorestrict H S.X₃ (Int.negSucc i) x) at hG
  change (tateFunctor H (Int.negSucc i + 1)).map (F.map f.τ₁)
    (subgroupIndShiftEquiv H S.X₃ (Int.negSucc i) x) =
      tateδ (subgroupRestrict_shortExact H hS) (Int.negSucc i) x at hH
  calc
    _ = tateCorestrict H S.X₁ (Int.negSucc i + 1)
        ((tateFunctor H (Int.negSucc i + 1)).map (F.map f.τ₁)
          (subgroupIndShiftEquiv H S.X₃ (Int.negSucc i) x)) :=
      congrArg (tateCorestrict H S.X₁ (Int.negSucc i + 1)) hH.symm
    _ = _ := by
      let a : Rep.indShiftDown S.X₃ ⟶ S.X₁ := f.τ₁
      exact (tateCorestrict_mapped_indShift H a i x).trans hG

/-- Corestriction commutes with the original connecting map of an underlying
split coefficient sequence in every integer degree. -/
theorem tateCorestrict_connecting {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (n : ℤ) (x : tate (Rep.res H.subtype S.X₃) n) :
    tateCorestrict H S.X₁ (n + 1) (tateδ (subgroupRestrict_shortExact H hS) n x) =
      tateδ hS n (tateCorestrict H S.X₃ n x) := by
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  cases n with
  | ofNat i =>
    let f := compareToCoindShift hS split
    let fH := F.mapShortComplex.map f
    let hD := Rep.coindShiftSequence_shortExact S.X₁
    have hf : f.τ₁ = 𝟙 S.X₁ := rfl
    have hfH : fH.τ₁ = 𝟙 (Rep.res H.subtype S.X₁) := F.map_id S.X₁
    have hG := tateδ_naturality_apply hS hD f i (tateCorestrict H S.X₃ i x)
    have hH := tateδ_naturality_apply (subgroupRestrict_shortExact H hS)
      (subgroupRestrict_shortExact H hD) fH i x
    have hG := (tate_map_endomorphism_apply_of_eq_id hf ((i : ℤ) + 1)
      (tateδ hS i (tateCorestrict H S.X₃ i x))).symm.trans hG
    have hH := (tate_map_endomorphism_apply_of_eq_id hfH ((i : ℤ) + 1)
      (tateδ (subgroupRestrict_shortExact H hS) i x)).symm.trans hH
    change tateδ hS i (tateCorestrict H S.X₃ i x) = coindShiftUpEquiv S.X₁ i
      ((tateFunctor G i).map f.τ₃ (tateCorestrict H S.X₃ i x)) at hG
    change tateδ (subgroupRestrict_shortExact H hS) i x =
      subgroupCoindShiftEquiv H S.X₁ i ((tateFunctor H i).map (F.map f.τ₃) x) at hH
    calc
      _ = tateCorestrict H S.X₁ ((i : ℤ) + 1)
          (subgroupCoindShiftEquiv H S.X₁ i ((tateFunctor H i).map (F.map f.τ₃) x)) :=
        congrArg (tateCorestrict H S.X₁ ((i : ℤ) + 1)) hH
      _ = _ := (tateCorestrict_coindShift H S.X₁ i _).trans
        ((congrArg (coindShiftUpEquiv S.X₁ i)
          (tateCorestrict_naturality H i f.τ₃ x).symm).trans hG.symm)
  | negSucc i => exact tateCorestrict_connecting_neg H hS split i x

end IntegralGroupCohomology.Universe
