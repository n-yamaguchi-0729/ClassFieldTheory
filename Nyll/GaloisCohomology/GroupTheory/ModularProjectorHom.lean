/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.MatrixProjectorExactness
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Field.ZMod

/-! # Hom out of a finite projective module computed by its matrix projector -/

@[expose] public section

open Matrix.Module
open scoped Matrix Ring

noncomputable section

namespace Module

variable {R J X V : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    [AddCommGroup X] [Module R X] [AddCommGroup V] [Module R V]
    (b : Basis J R X) (i : V →ₗ[R] X) (π : X →ₗ[R] V)

/-- The transpose matrix of the given projection. This is the action by
precomposition on the basis values of a map out of the free module. -/
def splitModuleProjector : Matrix J J R := (LinearMap.toMatrix b b (i.comp π))ᵀ

theorem splitModuleProjector_idempotent (h : π.comp i = LinearMap.id) :
    IsIdempotentElem (splitModuleProjector b i π) := by
  have h₀ : (i.comp π).comp (i.comp π) = i.comp π := by
    apply LinearMap.ext
    intro x
    exact congrArg i (LinearMap.congr_fun h (π x))
  change (LinearMap.toMatrix b b (i.comp π))ᵀ * (LinearMap.toMatrix b b (i.comp π))ᵀ = _
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp b b b, h₀]
  rfl

variable {W : Type*} [AddCommGroup W] [Module R W]

theorem splitModuleProjector_smul (x : J → W) (j : J) :
    (splitModuleProjector b i π • x) j = b.constr R x (i (π (b j))) := by
  rw [Matrix.Module.smul_apply, Basis.constr_apply_fintype]
  apply Finset.sum_congr rfl
  intro l _
  rw [splitModuleProjector, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    Basis.equivFun_apply, LinearMap.comp_apply]

/-- Evaluating a map out of the projective module on the projected basis
identifies it with the actual fixed vectors of the matrix projector. -/
def splitModuleProjector_homEquiv (h : π.comp i = LinearMap.id) :
    (V →ₗ[R] W) ≃ Matrix.projectorFixed (splitModuleProjector b i π) W where
  toFun f := ⟨fun j => f (π (b j)), by
    change splitModuleProjector b i π • (fun j => f (π (b j))) = _
    funext j
    rw [splitModuleProjector_smul,
      show b.constr R (fun j => f (π (b j))) = f.comp π from b.constr_eq R (fun _ => rfl)]
    exact congrArg f (LinearMap.congr_fun h (π (b j)))⟩
  invFun x := (b.constr R x.val).comp i
  left_inv f := by
    apply LinearMap.ext
    intro v
    change (b.constr R (fun j => f (π (b j)))) (i v) = f v
    rw [show b.constr R (fun j => f (π (b j))) = f.comp π from b.constr_eq R (fun _ => rfl)]
    exact congrArg f (LinearMap.congr_fun h v)
  right_inv x := by
    apply Subtype.ext
    funext j
    change (b.constr R x.val) (i (π (b j))) = x.val j
    rw [← splitModuleProjector_smul b i π]
    exact congrFun (Matrix.smul_projectorFixed _ W x) j

end Module

namespace MonoidAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- In the coprime case every finite coefficient module is represented by an
actual idempotent whose projected values compute the appropriate Hom groups. -/
theorem exists_modularHomProjector
    (G : Type*) [CommGroup G] [Finite G]
    (V : Type*) [AddCommGroup V] [Module (ZMod p)[G] V] [Module.Finite (ZMod p)[G] V]
    (hG : ¬ p ∣ Nat.card G) :
    ∃ (d : ℕ) (e : Matrix (Fin d) (Fin d) ((ZMod p)[G])), IsIdempotentElem e ∧
      ∀ (W : Type*) [AddCommGroup W] [Module (ZMod p)[G] W],
        Nonempty ((V →ₗ[(ZMod p)[G]] W) ≃ Matrix.projectorFixed e W) := by
  let : NeZero (Nat.card G : ZMod p) := ⟨fun h => hG ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  let : Module.Projective (ZMod p)[G] V := Module.projective_of_isSemisimpleRing (ZMod p)[G] V
  obtain ⟨d, F, I, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective (ZMod p)[G] V
  let b := Pi.basisFun ((ZMod p)[G]) (Fin d)
  exact ⟨d, Module.splitModuleProjector b I F, Module.splitModuleProjector_idempotent b I F h,
    fun W _ _ => ⟨Module.splitModuleProjector_homEquiv (W := W) b I F h⟩⟩

end MonoidAlgebra
