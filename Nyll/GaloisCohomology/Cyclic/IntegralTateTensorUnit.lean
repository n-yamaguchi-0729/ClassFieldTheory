/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateAbelianization
public import Nyll.GaloisCohomology.GroupTheory.RepresentationTensor

/-! # Unit isomorphisms for the original integral representation tensor -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

universe u v

variable {G : Type u} [Group G]

/-- The lifted integer carrier acts by the same scalar on the original coefficient. -/
def integerTensorLeftUnitIso (A : Rep.{v} ℤ G) :
    integralTrivialInteger.{u, v} G ⊗ᵣ A ≅ A := by
  let I := integralTrivialInteger.{u, v} G
  let e : (I ⊗ᵣ A : Rep.{v} ℤ G) ≃ₗ[ℤ] A :=
    (ULift.moduleEquiv : ULift.{v} ℤ ≃ₗ[ℤ] ℤ).rTensor A ≪≫ₗ TensorProduct.lid ℤ A
  have he (z : I) (a : A) : e (z ⊗ₜ[ℤ] a) = z.down • a := by
    change (TensorProduct.lid ℤ A)
      ((ULift.moduleEquiv : ULift.{v} ℤ ≃ₗ[ℤ] ℤ).rTensor A (z ⊗ₜ[ℤ] a)) = _
    rw [LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul, ULift.moduleEquiv_apply]
    exact int_smul_eq_zsmul A.hV2 z.down a
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply TensorProduct.ext'
  intro z a
  change e (TensorProduct.map (I.ρ g) (A.ρ g) (z ⊗ₜ[ℤ] a)) = A.ρ g (e (z ⊗ₜ[ℤ] a))
  rw [TensorProduct.map_tmul, he, he]
  have hz : I.ρ g z = z := rfl
  rw [hz]
  exact (map_zsmul (A.ρ g) z.down a).symm

/-- The same scalar action gives the right unit isomorphism on the original coefficient. -/
def integerTensorRightUnitIso (A : Rep.{v} ℤ G) :
    A ⊗ᵣ integralTrivialInteger.{u, v} G ≅ A :=
  Rep.diagonalTensorCommIso A (integralTrivialInteger G) ≪≫ integerTensorLeftUnitIso A

theorem integerTensorLeftUnitIso_tmul (A : Rep.{v} ℤ G)
    (z : integralTrivialInteger.{u, v} G) (a : A) :
    (integerTensorLeftUnitIso A).hom (z ⊗ₜ[ℤ] a) = z.down • a := by
  change (TensorProduct.lid ℤ A)
    ((ULift.moduleEquiv : ULift.{v} ℤ ≃ₗ[ℤ] ℤ).rTensor A (z ⊗ₜ[ℤ] a)) = _
  rw [LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul, ULift.moduleEquiv_apply]
  exact int_smul_eq_zsmul A.hV2 z.down a

theorem integerTensorRightUnitIso_tmul (A : Rep.{v} ℤ G)
    (a : A) (z : integralTrivialInteger.{u, v} G) :
    (integerTensorRightUnitIso A).hom (a ⊗ₜ[ℤ] z) = z.down • a :=
  (congrArg (fun x => (integerTensorLeftUnitIso A).hom x)
      (Rep.diagonalTensorCommIso_tmul A (integralTrivialInteger G) a z)).trans
    (integerTensorLeftUnitIso_tmul A z a)

/-- Left unit naturality for the exact same scalar action at each coefficient. -/
def integerTensorLeftUnitNatTrans (G : Type u) [Group G] :
    Rep.diagonalTensorLeft (integralTrivialInteger.{u, v} G) ⟶ 𝟭 (Rep.{v} ℤ G) where
  app A := (integerTensorLeftUnitIso A).hom
  naturality A B f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply TensorProduct.ext'
    intro z a
    change (integerTensorLeftUnitIso B).hom (Rep.diagonalTensorMap (𝟙 _) f (z ⊗ₜ[ℤ] a)) =
      f ((integerTensorLeftUnitIso A).hom (z ⊗ₜ[ℤ] a))
    rw [Rep.diagonalTensorMap_tmul, integerTensorLeftUnitIso_tmul, integerTensorLeftUnitIso_tmul]
    change z.down • f a = f (z.down • a)
    exact (map_zsmul f.hom z.down a).symm

end IntegralGroupCohomology.Universe
