/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Conjugation and restriction of literal finite monodromy

The coefficient formula for an actual finite Galois restriction determines
both its conjugation and its transition to an embedded subextension. These
computations retain the original ambient field automorphisms, so they can
be combined with the original Hilbert--Picard reciprocity squares.
-/

@[expose] public section

noncomputable section

universe u v w x y

namespace EtaleFundamentalGroups

/-- A finite monodromy with the original source coefficient formula
intertwines source conjugation with the actual semilinear conjugation of
the target extension. -/
theorem finiteGaloisMonodromy_conjugation_source
    {K : Type u} {Ω : Type v} {L : Type w} {H : Type x}
    [Field K] [Field Ω] [Field L] [Field H]
    [Algebra K Ω] [Algebra L H] [Algebra L Ω]
    {P Γ : Type*} [Group P] [Group Γ]
    (q : Gal(Ω/K) →* P) (π : P →* Γ)
    (i : H →ₐ[L] Ω) (χ : π.ker →* Gal(H/L))
    (hχ : ∀ (σ : Gal(Ω/K)) (hσ : π (q σ) = 1) (a : H),
      i (χ ⟨q σ, hσ⟩ a) = σ (i a))
    (ρ : Gal(Ω/K)) (eL : L ≃+* L) (eH : H ≃+* H)
    (hbase : ∀ a : L, eH (algebraMap L H a) = algebraMap L H (eL a))
    (hambient : ∀ a : H, i (eH a) = ρ (i a))
    (σ : Gal(Ω/K)) (hσ : π (q σ) = 1) :
    χ (MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩) =
      LocalClassFieldTheory.semilinearGaloisGroupCongr L L H H eL eH hbase
        (χ ⟨q σ, hσ⟩) := by
  have hconj : π (q (ρ * σ * ρ⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      hσ, mul_one, mul_inv_cancel]
  have hsource : (⟨q (ρ * σ * ρ⁻¹), hconj⟩ : π.ker) =
      MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩ := by
    apply Subtype.ext
    change q (ρ * σ * ρ⁻¹) = q ρ * q σ * (q ρ)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [← hsource]
  apply AlgEquiv.ext
  intro a
  obtain ⟨b, rfl⟩ := eH.surjective a
  apply i.injective
  calc
    i (χ ⟨q (ρ * σ * ρ⁻¹), hconj⟩ (eH b)) =
        (ρ * σ * ρ⁻¹) (i (eH b)) := hχ _ hconj _
    _ = ρ (σ (i b)) := by
      change ρ (σ (ρ.symm (i (eH b)))) = _
      rw [hambient, ρ.symm_apply_apply]
    _ = ρ (i (χ ⟨q σ, hσ⟩ b)) := congrArg ρ (hχ σ hσ b).symm
    _ = i (eH (χ ⟨q σ, hσ⟩ b)) := (hambient _).symm
    _ = i (LocalClassFieldTheory.semilinearGaloisGroupCongr L L H H eL eH hbase
        (χ ⟨q σ, hσ⟩) (eH b)) :=
      congrArg i (LocalClassFieldTheory.semilinearGaloisGroupCongr_apply_equiv
        L L H H eL eH hbase (χ ⟨q σ, hσ⟩) b).symm

/-- Two finite actions with the same actual ambient coefficient action
agree under literal Galois restriction through an embedded subextension. -/
theorem finiteGaloisRestriction_eq_of_coefficient_action
    {K : Type u} {L : Type v} {H₀ : Type w} {H₁ : Type x} {Ω : Type y}
    [Field K] [Field L]
    [Field H₀] [Field H₁] [Field Ω]
    [Algebra K L] [Algebra K H₀] [Algebra L H₁]
    [Algebra K H₁] [IsScalarTower K L H₁]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsGalois K H₀]
    (i₀ : H₀ →ₐ[K] Ω) (i₁ : H₁ →ₐ[L] Ω)
    (j : H₀ →ₐ[K] H₁) :
    let _ : Algebra H₀ H₁ := j.toRingHom.toAlgebra
    let _ : IsScalarTower K H₀ H₁ :=
      IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
    ∀ (_ : ∀ a : H₀, i₁ (j a) = i₀ a)
      (τ : Ω ≃+* Ω) (σ₀ : Gal(H₀/K)) (σ₁ : Gal(H₁/L)),
      (∀ a : H₀, i₀ (σ₀ a) = τ (i₀ a)) →
      (∀ a : H₁, i₁ (σ₁ a) = τ (i₁ a)) →
      AlgEquiv.restrictNormalHom H₀ (σ₁.restrictScalars K) = σ₀ := by
  intro aH₀H₁ hKH₀H₁ hj τ σ₀ σ₁ hσ₀ hσ₁
  apply AlgEquiv.ext
  intro a
  apply i₀.injective
  calc
    i₀ ((AlgEquiv.restrictNormalHom H₀ (σ₁.restrictScalars K)) a) =
        i₁ (j ((AlgEquiv.restrictNormalHom H₀ (σ₁.restrictScalars K)) a)) :=
      (hj _).symm
    _ = i₁ (σ₁ (j a)) := congrArg i₁
      (AlgEquiv.restrictNormal_commutes (σ₁.restrictScalars K) H₀ a)
    _ = τ (i₁ (j a)) := hσ₁ (j a)
    _ = τ (i₀ a) := congrArg τ (hj a)
    _ = i₀ (σ₀ a) := (hσ₀ a).symm

end EtaleFundamentalGroups
