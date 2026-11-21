/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), The Tau Ceti contributors

The comparison with split sequences follows Tau Ceti's
`RepresentationTheory/Homological/TateCohomology/Cup/Delta.lean`.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCup
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.IntegralTateSplitSequences
public import Nyll.GaloisCohomology.GroupTheory.TensorShiftExactness

/-!
# The cup product and connecting maps of split coefficient sequences

In the second variable, the original Tate connecting map satisfies the
signed cup formula for every sequence split on the underlying ℤ-modules.
The proof uses the retraction or the section to compare the given sequence
with the canonical coinduced or induced sequence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G]

variable [Fintype G]

private theorem tateCup_connecting_right_nonneg (A : Rep.{u} ℤ G) {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (hq : 0 ≤ q) (h : p + q = r) (x : tate A p) (y : tate S.X₃ q) :
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A split
    tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y) =
      p.negOnePow • tateδ hT r (tateCup A S.X₃ p q r h x y) := by
  intro hT
  let f := compareToCoindShift hS split
  have hf : f.τ₁ = 𝟙 S.X₁ := rfl
  let F := tateFunctor G (q + 1)
  let hD := Rep.coindShiftSequence_shortExact S.X₁
  have hm : F.map f.τ₁ = 𝟙 (tate S.X₁ (q + 1)) :=
    (congrArg F.map hf).trans (F.map_id S.X₁)
  have hδ₀ : F.map f.τ₁ (tateδ hS q y) = tateδ hD q ((tateFunctor G q).map f.τ₃ y) :=
    congrArg (fun m : tate S.X₃ q ⟶ tate S.X₁ (q + 1) => m y)
      (tateδ_naturality hS hD f q)
  have hδ : tateδ hS q y = coindShiftUpEquiv S.X₁ q ((tateFunctor G q).map f.τ₃ y) :=
    (congrArg (fun m : tate S.X₁ (q + 1) ⟶ tate S.X₁ (q + 1) =>
      m (tateδ hS q y)) hm).symm.trans hδ₀
  have hcup := tateCup_naturality (𝟙 A) f.τ₃ p q r h x y
  simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply] at hcup
  let z := tateCup A S.X₃ p q r h x y
  let T := Rep.diagonalTensorLeft A ⋙ tateFunctor G (r + 1)
  have hid : T.map f.τ₁ = 𝟙 (T.obj S.X₁) :=
    (congrArg T.map hf).trans (T.map_id S.X₁)
  have ha := congrArg (fun m : T.obj S.X₁ ⟶ T.obj S.X₁ => m (tateδ hT r z)) hid
  have ht : tateδ hT r z =
      tensorCoindShiftEquiv A S.X₁ r ((tateFunctor G r).map (𝟙 A ⊗ᵣₘ f.τ₃) z) :=
    ha.symm.trans (tateδ_tensor_naturality (𝟙 A) f hT
      (Rep.tensorLeft_coindShiftSequence_shortExact A S.X₁) r z)
  rw [hδ]
  refine (tateCup_coindShift_connecting A S.X₁ hq h x _).trans ?_
  exact congrArg (fun w => p.negOnePow • tensorCoindShiftEquiv A S.X₁ r w) hcup.symm |>.trans
    (congrArg (p.negOnePow • ·) ht.symm)

private theorem tateCup_mapped_indShift_connecting (A B C : Rep.{u} ℤ G)
    (f : Rep.indShiftDown B ⟶ C) {p q r : ℤ} (hq : q < 0) (h : p + q = r)
    (x : tate A p) (y : tate B q) :
    tateCup A C p (q + 1) (r + 1) (by omega) x
        ((tateFunctor G (q + 1)).map f (indShiftDownEquiv B q y)) =
      p.negOnePow • (tateFunctor G (r + 1)).map (𝟙 A ⊗ᵣₘ f)
        (tensorIndShiftEquiv A B r (tateCup A B p q r h x y)) := by
  let m := (tateFunctor G (r + 1)).map (𝟙 A ⊗ᵣₘ f)
  have hcup := tateCup_naturality (𝟙 A) f p (q + 1) (r + 1) (by omega) x
    (indShiftDownEquiv B q y)
  simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply] at hcup
  refine hcup.symm.trans ((congrArg (fun w : tate (A ⊗ᵣ Rep.indShiftDown B) (r + 1) => m w)
    (tateCup_indShift_connecting A B hq h x y)).trans ?_)
  simp only [Units.smul_def]
  exact m.hom.toAddMonoidHom.map_zsmul (p.negOnePow : ℤ) _

private theorem mappedIndShiftDown_eq_boundary {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (f : Rep.indShiftSequence S.X₃ ⟶ S) (hf : f.τ₃ = 𝟙 S.X₃)
    (n : ℤ) (x : tate S.X₃ n) :
    (tateFunctor G (n + 1)).map f.τ₁ (indShiftDownEquiv S.X₃ n x) = tateδ hS n x := by
  let F := tateFunctor G n
  have hmap : F.map f.τ₃ = 𝟙 (tate S.X₃ n) :=
    (congrArg F.map hf).trans (F.map_id S.X₃)
  have hδ := congrArg (fun m : tate S.X₃ n ⟶ tate S.X₁ (n + 1) => m x)
    (tateδ_naturality (Rep.indShiftSequence_shortExact S.X₃) hS f n)
  exact hδ.trans (congrArg (fun m : tate S.X₃ n ⟶ tate S.X₃ n => tateδ hS n (m x)) hmap)

private theorem mappedTensorIndShiftDown_eq_boundary (A : Rep.{u} ℤ G)
    {S : ShortComplex (Rep.{u} ℤ G)} (hT : (S.map (Rep.diagonalTensorLeft A)).ShortExact)
    (f : Rep.indShiftSequence S.X₃ ⟶ S) (hf : f.τ₃ = 𝟙 S.X₃)
    (n : ℤ) (x : tate (A ⊗ᵣ S.X₃) n) :
    (tateFunctor G (n + 1)).map (𝟙 A ⊗ᵣₘ f.τ₁) (tensorIndShiftEquiv A S.X₃ n x) =
      tateδ hT n x := by
  let T := Rep.diagonalTensorLeft A ⋙ tateFunctor G n
  have hid : T.map f.τ₃ = 𝟙 (T.obj S.X₃) :=
    (congrArg T.map hf).trans (T.map_id S.X₃)
  have hδ := tateδ_tensor_naturality (𝟙 A) f
    (Rep.tensorLeft_indShiftSequence_shortExact A S.X₃) hT n x
  have ha := congrArg (fun m : T.obj S.X₃ ⟶ T.obj S.X₃ => tateδ hT n (m x)) hid
  exact hδ.trans ha

private theorem tateCup_connecting_right_neg (A : Rep.{u} ℤ G) {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (hq : q < 0) (h : p + q = r) (x : tate A p) (y : tate S.X₃ q) :
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A split
    tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y) =
      p.negOnePow • tateδ hT r (tateCup A S.X₃ p q r h x y) := by
  intro hT
  let f := compareFromIndShift hS split
  have hf : f.τ₃ = 𝟙 S.X₃ := rfl
  have hδ := mappedIndShiftDown_eq_boundary hS f hf q y
  have ht := mappedTensorIndShiftDown_eq_boundary A hT f hf r (tateCup A S.X₃ p q r h x y)
  have hcup := tateCup_mapped_indShift_connecting A S.X₃ S.X₁ f.τ₁ hq h x y
  exact (congrArg (tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x) hδ.symm).trans
    (hcup.trans (congrArg (p.negOnePow • ·) ht))

/-- The cup rule in the second variable for a short exact coefficient sequence
with a splitting on the underlying modules. -/
theorem tateCup_connecting_right (A : Rep.{u} ℤ G) {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate A p) (y : tate S.X₃ q) :
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A split
    tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y) =
      p.negOnePow • tateδ hT r (tateCup A S.X₃ p q r h x y) := by
  by_cases hq : 0 ≤ q
  · exact tateCup_connecting_right_nonneg A hS split hq h x y
  · exact tateCup_connecting_right_neg A hS split (lt_of_not_ge hq) h x y

/-- Cup with a class of degree zero commutes with the connecting map in the
left variable. It is the naturality square for the actual fixed coefficient. -/
theorem tateCupZeroRight_connecting_left (B : Rep.{u} ℤ G)
    {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (hT : (S.map (Rep.diagonalTensorRight B)).ShortExact) (p : ℤ)
    (x : tate S.X₃ p) (y : tate B 0) :
    tensorCupZeroRight S.X₁ B (p + 1) (tateδ hS p x) y =
      tateδ hT p (tensorCupZeroRight S.X₃ B p x y) := by
  obtain ⟨b, rfl⟩ := fixedClass_surjective B y
  rw [tensorCupZeroRight_fixedClass, tensorCupZeroRight_fixedClass]
  let i : 𝟭 (Rep.{u} ℤ G) ⟶ Rep.diagonalTensorRight B := {
    app := fun A => Rep.tensorInvariant A B b
    naturality := fun A C f => by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro a
      change (f a ⊗ₜ[ℤ] (b : B)) = f.hom.toLinearMap.rTensor B (a ⊗ₜ[ℤ] (b : B))
      rw [LinearMap.rTensor_tmul]
      rfl }
  exact congrArg (fun m : tate S.X₃ p ⟶ tate (S.X₁ ⊗ᵣ B) (p + 1) => m x)
    (tateδ_naturality hS hT (S.mapNatTrans i) p)

end IntegralGroupCohomology.Universe
