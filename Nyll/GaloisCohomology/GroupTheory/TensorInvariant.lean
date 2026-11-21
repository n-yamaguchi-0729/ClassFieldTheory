/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.FiniteGroupTrace
public import Nyll.GaloisCohomology.GroupTheory.RepresentationTensor
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Tensoring with an invariant coefficient

The original tensor representation is used directly. Tensoring with a norm
is the existing coefficient trace of tensoring with its preimage after
restriction to the trivial subgroup.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory
open scoped TensorProduct BigOperators RepTensor

namespace Rep

variable {R : Type r} {G : Type u} [CommRing R] [Group G]

/-- Tensoring on the right with an invariant is a morphism of the original
representations, using the actual diagonal tensor action. -/
def tensorInvariant (A B : Rep.{v} R G) (y : B.ρ.invariants) :
    A ⟶ A ⊗ᵣ B :=
  Rep.ofHom ⟨(TensorProduct.mk R A B).flip (y : B), fun g => by
    apply LinearMap.ext
    intro a
    change A.ρ g a ⊗ₜ[R] (y : B) =
      TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[R] (y : B))
    rw [TensorProduct.map_tmul, y.property g]⟩

/-- The equivariant map has the original elementary tensor as its value. -/
theorem tensorInvariant_apply (A B : Rep.{v} R G) (y : B.ρ.invariants) (a : A) :
    (tensorInvariant A B y).hom a = a ⊗ₜ[R] (y : B) := rfl

/-- The tensor morphism depends linearly on the invariant coefficient. -/
def tensorInvariantLinear (A B : Rep.{v} R G) :
    B.ρ.invariants →ₗ[R] (A ⟶ A ⊗ᵣ B) where
  toFun := tensorInvariant A B
  map_add' y z := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    exact map_add ((TensorProduct.mk R A B) a) (y : B) (z : B)
  map_smul' c y := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    exact map_smul ((TensorProduct.mk R A B) a) c (y : B)

/-- Any coefficient defines the same tensor map after restriction to the
trivial subgroup; no invariance condition is required there. -/
def tensorTrivialSubgroupMap (A B : Rep.{v} R G) (z : B) :
    res (⊥ : Subgroup G).subtype A ⟶
      res (⊥ : Subgroup G).subtype (A ⊗ᵣ B) :=
  Rep.ofHom ⟨(TensorProduct.mk R A B).flip z, fun g => by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    simp only [map_one]
    change ((TensorProduct.mk R A B).flip z).comp LinearMap.id =
      LinearMap.id.comp ((TensorProduct.mk R A B).flip z)
    rw [LinearMap.comp_id, LinearMap.id_comp]⟩

/-- If the invariant is a norm, its tensor map is the actual finite-index
trace of the restricted tensor map. -/
theorem tensorInvariant_eq_trace_of_norm [Fintype G]
    (A B : Rep.{max r u v} R G) (y : B.ρ.invariants) (z : B)
    (hy : (y : B) = B.ρ.norm z) :
    tensorInvariant A B y =
      ClassFieldTower.Cohomology.finiteIndexHomTrace.{r, u, v}
        (A ⊗ᵣ B) (⊥ : Subgroup G) A
        (tensorTrivialSubgroupMap A B z) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro a
  rw [ClassFieldTower.Cohomology.finiteIndexHomTrace_bot_apply]
  change a ⊗ₜ[R] (y : B) =
    ∑ g : G, (A.ρ.tprod B.ρ) g⁻¹ (A.ρ g a ⊗ₜ[R] z)
  rw [hy]
  simp only [Representation.tprod_apply, TensorProduct.map_tmul,
    ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  rw [← TensorProduct.tmul_sum]
  apply congrArg (fun b : B => a ⊗ₜ[R] b)
  change B.ρ.norm z = ∑ g : G, B.ρ g⁻¹ z
  rw [Representation.norm, LinearMap.sum_apply]
  exact (Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)).symm

end Rep
