/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGalois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionLinearDisjoint
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants

/-!
# Galois groups and Frobenius of actual constant-field extensions

The field is the compositum inside the chosen ambient field, formed by adjoining
the constants to the original function field. Restriction to the constants is
injective. When the base already contains all separable constants, the proved
degree formula makes restriction an isomorphism. Transporting the finite-field
Frobenius along this isomorphism gives its actual automorphism over the function
field, with the expected order and action on constants.

The final specialization uses the actual full constant field of any finite-base
function field; the separable-constants condition is then a proved theorem.
-/

noncomputable section

namespace FunctionField

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Finite k] (C : IntermediateField k Ω) [FiniteDimensional k C]

/-- Restrict an automorphism of the actual constant compositum to its constants. -/
def constantExtensionRestriction :
    ((IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω))) →* (C ≃ₐ[k] C) :=
  let _aC : Algebra C (IntermediateField.adjoin K (C : Set Ω)) := constantAlgebra (K := K) C
  have : IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantScalarTower (K := K) C
  have : Finite C := Module.finite_of_finite k
  (AlgEquiv.restrictNormalHom C).comp (AlgEquiv.restrictScalarsHom k)

/-- Restriction is defined using the actual embedding of the constant field. -/
theorem constantExtensionRestriction_commutes
    (σ : (IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω))) (c : C) :
    constantEmbedding (K := K) C (constantExtensionRestriction (K := K) C σ c) =
      σ (constantEmbedding (K := K) C c) := by
  let _aC : Algebra C (IntermediateField.adjoin K (C : Set Ω)) := constantAlgebra (K := K) C
  have : IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantScalarTower (K := K) C
  have : Finite C := Module.finite_of_finite k
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) C c

/-- An automorphism fixing the function field is determined by its action on the
adjoined constants. -/
theorem constantExtensionRestriction_injective :
    Function.Injective (constantExtensionRestriction (K := K) C) := by
  intro σ τ h
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro x hx
  change σ (constantEmbedding (K := K) C ⟨x, hx⟩) = τ (constantEmbedding (K := K) C ⟨x, hx⟩)
  rw [← constantExtensionRestriction_commutes, ← constantExtensionRestriction_commutes, h]

/-- Every finite constant-field compositum is a cyclic extension. This does not
require that the original choice of constants was already full. -/
theorem isCyclic_constantExtension :
    IsCyclic ((IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω))) := by
  have : Finite C := Module.finite_of_finite k
  exact isCyclic_of_injective (constantExtensionRestriction (K := K) C)
    (constantExtensionRestriction_injective (K := K) C)

variable (hsc : ∀ y : K, IsSeparable k y → y ∈ (algebraMap k K).range)

include hsc in
/-- With full separable constants, every automorphism of the constants extends
uniquely over the original function field. -/
theorem constantExtensionRestriction_bijective :
    Function.Bijective (constantExtensionRestriction (K := K) C) := by
  have : Finite C := Module.finite_of_finite k
  have : FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) :=
    finiteDimensional_constantExtension_of_finite (K := K) C
  have : IsGalois K (IntermediateField.adjoin K (C : Set Ω)) :=
    isGalois_constantExtension (K := K) C
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨constantExtensionRestriction_injective (K := K) C, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    finrank_constantExtension (K := K) C hsc]

/-- The Galois group of the actual constant extension is the Galois group of its constants. -/
def constantExtensionGaloisEquiv :
    ((IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω))) ≃* (C ≃ₐ[k] C) :=
  MulEquiv.ofBijective (constantExtensionRestriction (K := K) C)
    (constantExtensionRestriction_bijective (K := K) C hsc)

section Frobenius

variable [Fintype k]

/-- The arithmetic Frobenius of the actual constant-field extension. -/
def constantExtensionFrobenius :
    (IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω)) :=
  (constantExtensionGaloisEquiv (K := K) C hsc).symm (FiniteField.frobeniusAlgEquivOfAlgebraic k C)

/-- The arithmetic Frobenius raises each constant to the cardinality of the base. -/
theorem constantExtensionFrobenius_constant (c : C) :
    constantExtensionFrobenius (K := K) C hsc (constantEmbedding (K := K) C c) =
      constantEmbedding (K := K) C (c ^ Fintype.card k) := by
  rw [← constantExtensionRestriction_commutes]
  change constantEmbedding (K := K) C
      ((constantExtensionGaloisEquiv (K := K) C hsc)
        ((constantExtensionGaloisEquiv (K := K) C hsc).symm
          (FiniteField.frobeniusAlgEquivOfAlgebraic k C)) c) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Frobenius has precisely the degree of the constant extension as its order. -/
theorem orderOf_constantExtensionFrobenius :
    orderOf (constantExtensionFrobenius (K := K) C hsc) = Module.finrank k C := by
  have : Finite C := Module.finite_of_finite k
  exact ((constantExtensionGaloisEquiv (K := K) C hsc).symm.orderOf_eq
    (FiniteField.frobeniusAlgEquivOfAlgebraic k C)).trans
      (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k C)

/-- Every automorphism is a power of the actual arithmetic Frobenius. -/
theorem exists_pow_constantExtensionFrobenius
    (σ : (IntermediateField.adjoin K (C : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (C : Set Ω))) :
    ∃ n : Fin (Module.finrank k C), constantExtensionFrobenius (K := K) C hsc ^ n.val = σ := by
  have : Finite C := Module.finite_of_finite k
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k C).surjective
    (constantExtensionGaloisEquiv (K := K) C hsc σ)
  refine ⟨n, (constantExtensionGaloisEquiv (K := K) C hsc).injective ?_⟩
  rw [map_pow]
  change ((constantExtensionGaloisEquiv (K := K) C hsc)
    ((constantExtensionGaloisEquiv (K := K) C hsc).symm
      (FiniteField.frobeniusAlgEquivOfAlgebraic k C))) ^ n.val = _
  rw [MulEquiv.apply_symm_apply]
  exact hn

end Frobenius

section FullConstants

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- For an arbitrary finite-base function field, the actual full constant field
discharges the constants hypothesis in the Galois group comparison. -/
def fullConstantExtensionGaloisEquiv
    (D : IntermediateField (algebraicClosure k K) Ω)
    [FiniteDimensional (algebraicClosure k K) D] :
    ((IntermediateField.adjoin K (D : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (D : Set Ω))) ≃*
        (D ≃ₐ[algebraicClosure k K] D) :=
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  constantExtensionGaloisEquiv D (separableConstants_fullConstants k K)

/-- Arithmetic Frobenius after replacing an arbitrary finite base by its proved
full constant field. The automorphism fixes the original function field. -/
def fullConstantExtensionFrobenius
    (D : IntermediateField (algebraicClosure k K) Ω)
    [FiniteDimensional (algebraicClosure k K) D] :
    (IntermediateField.adjoin K (D : Set Ω)) ≃ₐ[K]
      (IntermediateField.adjoin K (D : Set Ω)) :=
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let _ : Fintype (algebraicClosure k K) := Fintype.ofFinite _
  constantExtensionFrobenius D (separableConstants_fullConstants k K)

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- Frobenius on the full constants raises them to the cardinality of the actual
full constant field, even when the initial finite base was smaller. -/
theorem fullConstantExtensionFrobenius_constant
    (D : IntermediateField (algebraicClosure k K) Ω)
    [FiniteDimensional (algebraicClosure k K) D] (c : D) :
    fullConstantExtensionFrobenius (k := k) D (constantEmbedding (K := K) D c) =
      constantEmbedding (K := K) D (c ^ Nat.card (algebraicClosure k K)) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let _ : Fintype (algebraicClosure k K) := Fintype.ofFinite _
  simpa only [fullConstantExtensionFrobenius, Nat.card_eq_fintype_card] using
    constantExtensionFrobenius_constant D (separableConstants_fullConstants k K) c

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- Powers of arithmetic Frobenius act on the actual embedded constants by the
corresponding power of their cardinality. -/
theorem fullConstantExtensionFrobenius_pow_constant
    (D : IntermediateField (algebraicClosure k K) Ω)
    [FiniteDimensional (algebraicClosure k K) D] (m : ℕ) (c : D) :
    (fullConstantExtensionFrobenius (k := k) D ^ m) (constantEmbedding (K := K) D c) =
      constantEmbedding (K := K) D (c ^ Nat.card (algebraicClosure k K) ^ m) := by
  induction m with
  | zero => simp only [pow_zero, AlgEquiv.one_apply, pow_one]
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, fullConstantExtensionFrobenius_constant,
      ← pow_mul, ← pow_succ]

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- The order of the full-constant Frobenius is the actual extension degree over
the original function field. -/
theorem orderOf_fullConstantExtensionFrobenius
    (D : IntermediateField (algebraicClosure k K) Ω)
    [FiniteDimensional (algebraicClosure k K) D] :
    orderOf (fullConstantExtensionFrobenius (k := k) D) =
      Module.finrank K (IntermediateField.adjoin K (D : Set Ω)) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let _ : Fintype (algebraicClosure k K) := Fintype.ofFinite _
  exact (orderOf_constantExtensionFrobenius D
    (separableConstants_fullConstants k K)).trans
      (finrank_constantExtension D (separableConstants_fullConstants k K)).symm

end FullConstants

end FunctionField
