/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The original diagonal tensor in the representation carrier universe -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Rep

universe r u v

variable {R : Type r} {G : Type u} [CommRing R] [Group G]

/-- The diagonal representation on the ordinary tensor product of the two carriers. -/
def diagonalTensor (A B : Rep.{v} R G) : Rep.{v} R G :=
  Rep.of (A.ρ.tprod B.ρ)

scoped[RepTensor] infixr:70 " ⊗ᵣ " => Rep.diagonalTensor

open scoped RepTensor

theorem diagonalTensor_ρ (A B : Rep.{v} R G) : (A ⊗ᵣ B).ρ = A.ρ.tprod B.ρ := rfl

/-- The original tensor of the two equivariant maps. -/
def diagonalTensorMap {A A' B B' : Rep.{v} R G} (f : A ⟶ A') (g : B ⟶ B') :
    A ⊗ᵣ B ⟶ A' ⊗ᵣ B' :=
  Rep.ofHom (f.hom.tensor g.hom)

theorem diagonalTensorMap_tmul {A A' B B' : Rep.{v} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : A) (b : B) :
    diagonalTensorMap f g (a ⊗ₜ[R] b) = f a ⊗ₜ[R] g b :=
  TensorProduct.map_tmul _ _ _ _

scoped[RepTensor] infixr:70 " ⊗ᵣₘ " => Rep.diagonalTensorMap

/-- The tensor of two composite maps is the composite of their tensors. -/
theorem diagonalTensorMap_comp {A A' A'' B B' B'' : Rep.{v} R G}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    diagonalTensorMap f g ≫ diagonalTensorMap f' g' =
      diagonalTensorMap (f ≫ f') (g ≫ g') := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  exact (TensorProduct.map_comp _ _ _ _).symm

/-- Left diagonal tensor as a functor on the original representations. -/
def diagonalTensorLeft (A : Rep.{v} R G) : Rep.{v} R G ⥤ Rep.{v} R G where
  obj B := A ⊗ᵣ B
  map f := diagonalTensorMap (𝟙 A) f
  map_id B := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    exact TensorProduct.map_id
  map_comp f g := by
    rw [diagonalTensorMap_comp, Category.id_comp]

/-- Right diagonal tensor as a functor on the original representations. -/
def diagonalTensorRight (B : Rep.{v} R G) : Rep.{v} R G ⥤ Rep.{v} R G where
  obj A := A ⊗ᵣ B
  map f := diagonalTensorMap f (𝟙 B)
  map_id A := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    exact TensorProduct.map_id
  map_comp f g := by
    rw [diagonalTensorMap_comp, Category.id_comp]

instance diagonalTensorLeft_additive (A : Rep.{v} R G) : (diagonalTensorLeft A).Additive where
  map_add := fun {X Y} {f g : X ⟶ Y} => by
    let e : A.ρ.IntertwiningMap A.ρ := Representation.IntertwiningMap.id A.ρ
    apply Rep.hom_ext
    change e.tensor (f.hom + g.hom) = e.tensor f.hom + e.tensor g.hom
    exact Representation.IntertwiningMap.tensor_add_right e f.hom g.hom

instance diagonalTensorRight_additive (B : Rep.{v} R G) : (diagonalTensorRight B).Additive where
  map_add := fun {X Y} {f g : X ⟶ Y} => by
    let e : B.ρ.IntertwiningMap B.ρ := Representation.IntertwiningMap.id B.ρ
    apply Rep.hom_ext
    change (f.hom + g.hom).tensor e = f.hom.tensor e + g.hom.tensor e
    exact Representation.IntertwiningMap.tensor_add_left f.hom g.hom e

theorem diagonalTensorMap_id (A B : Rep.{v} R G) :
    diagonalTensorMap (𝟙 A) (𝟙 B) = 𝟙 (A ⊗ᵣ B) :=
  (diagonalTensorLeft A).map_id B

/-- Swapping the two original tensor factors preserves the diagonal action. -/
def diagonalTensorCommIso (A B : Rep.{v} R G) : A ⊗ᵣ B ≅ B ⊗ᵣ A := by
  let e : (A ⊗ᵣ B : Rep.{v} R G) ≃ₗ[R] (B ⊗ᵣ A : Rep.{v} R G) :=
    TensorProduct.comm R A B
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply TensorProduct.ext'
  intro a b
  change e (TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[R] b)) =
    TensorProduct.map (B.ρ g) (A.ρ g) (e (a ⊗ₜ[R] b))
  rw [TensorProduct.map_tmul]
  change TensorProduct.comm R A B ((A.ρ g) a ⊗ₜ[R] (B.ρ g) b) =
    TensorProduct.map (B.ρ g) (A.ρ g) (TensorProduct.comm R A B (a ⊗ₜ[R] b))
  rw [TensorProduct.comm_tmul R A B, TensorProduct.comm_tmul R A B, TensorProduct.map_tmul]

theorem diagonalTensorCommIso_tmul (A B : Rep.{v} R G) (a : A) (b : B) :
    (diagonalTensorCommIso A B).hom (a ⊗ₜ[R] b) = b ⊗ₜ[R] a :=
  TensorProduct.comm_tmul R A B a b

/-- A map of left factors induces a transformation on diagonal tensor functors. -/
def diagonalTensorLeftNatTrans {A B : Rep.{v} R G} (f : A ⟶ B) :
    diagonalTensorLeft A ⟶ diagonalTensorLeft B where
  app C := diagonalTensorMap f (𝟙 C)
  naturality C D g := by
    change diagonalTensorMap (𝟙 A) g ≫ diagonalTensorMap f (𝟙 D) =
      diagonalTensorMap f (𝟙 C) ≫ diagonalTensorMap (𝟙 B) g
    rw [diagonalTensorMap_comp, diagonalTensorMap_comp, Category.id_comp, Category.comp_id,
      Category.comp_id, Category.id_comp]

end Rep
