/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertGaloisNorm
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteGaloisMonodromyOperations

/-!
# Norm compatibility for the original source actions on Hilbert fields

The actual upper Hilbert image contains the actual lower one. Restricting
the original embeddings therefore constructs a coefficient-compatible
Hilbert-field embedding. Two finite Galois actions induced by the same
ambient source automorphism then satisfy the original Picard norm formula.
No coherence of independently chosen monodromy maps is assumed.
-/

@[expose] public section

noncomputable section

universe u v w x y z

open AlgebraicCurve

namespace FunctionField

variable {k : Type u} {C : Type v} {E : Type w} {K : Type x} {L : Type y}
    [Field k] [Finite k] [Field C] [Field E]
    [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Algebra k C] [Algebra C K] [IsScalarTower k C K] [Module.Finite k C]
    [Algebra k E] [Algebra E L] [IsScalarTower k E L] [Algebra.IsIntegral k E]
    [Algebra C E] [IsScalarTower k C E] [Algebra.IsIntegral C E]
    [Algebra C L] [IsScalarTower k C L] [IsScalarTower C E L] [IsScalarTower C K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [HasPrincipalDivisors C K] [HasPrincipalDivisors C L] [HasPrincipalDivisors E L]

omit [IsScalarTower k C E] in
/-- Source actions on the two actual pointed Hilbert fields satisfy the
actual constant-stage Picard norm formula. The required Hilbert embedding
and its coefficient square are both constructed from the original images. -/
theorem constantHilbertPicard_norm_of_common_source
    (v : Place C K) (hv : v.deg = 1) (w : Place E L) (hw : w.deg = 1)
    (hplace : w.restrictConstants K = v)
    (Ω : Type z) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] :
    let H₀ := hilbertClassField k K {v.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    let H₁ := hilbertClassField k L {w.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    ∀ (i₀ : H₀.val →ₐ[K] Ω) (i₁ : H₁.val →ₐ[L] Ω)
      (τ : Ω ≃+* Ω) (σ₀ : Gal(H₀.val/K)) (σ₁ : Gal(H₁.val/L)),
      (∀ a : H₀.val, i₀ (σ₀ a) = τ (i₀ a)) →
      (∀ a : H₁.val, i₁ (σ₁ a) = τ (i₁ a)) →
      H1Gm.ofPic0 C K
          ((constantHilbertClassFieldGaloisEquivPic0 k C K v hv) σ₀).toAdd =
        Pic.normConstants C E K L
          (H1Gm.ofPic0 E L
            ((constantHilbertClassFieldGaloisEquivPic0 k E L w hw) σ₁).toAdd) := by
  intro H₀ H₁ i₀ i₁ τ σ₀ σ₁ hσ₀ hσ₁
  let aKH₁ : Algebra K H₁.val :=
    ((algebraMap L H₁.val).comp (algebraMap K L)).toAlgebra
  have hKLH₁ : IsScalarTower K L H₁.val :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hrestrict : (w.forgetConstants (K := k)).restrict K =
      v.forgetConstants (K := k) := by
    apply Place.ext
    have hvaluation : (w.restrictConstants K).toValuationSubring = v.toValuationSubring :=
      congrArg (fun p : Place C K => p.toValuationSubring) hplace
    exact hvaluation
  have hsplit : ∀ z ∈ ({w.forgetConstants (K := k)} : Finset (Place k L)),
      z.restrict K ∈ ({v.forgetConstants (K := k)} : Finset (Place k K)) := by
    intro z hz
    rw [Finset.mem_singleton.mp hz, hrestrict]
    exact Finset.mem_singleton_self _
  let j₁ := i₁.restrictScalars K
  have hmono : i₀.fieldRange ≤ j₁.fieldRange := hilbertClassFieldImage_mono
    {v.forgetConstants (K := k)} (Finset.singleton_nonempty _)
    {w.forgetConstants (K := k)} (Finset.singleton_nonempty _) hsplit Ω i₀ i₁
  let j : H₀.val →ₐ[K] H₁.val := j₁.equivFieldRange.symm.toAlgHom.comp
    (i₀.codRestrict j₁.fieldRange.toSubalgebra (fun a => hmono ⟨a, rfl⟩))
  have hj (a : H₀.val) : i₁ (j a) = i₀ a :=
    congrArg Subtype.val (j₁.equivFieldRange.apply_symm_apply
      ⟨i₀ a, hmono ⟨a, rfl⟩⟩)
  let aH₀H₁ : Algebra H₀.val H₁.val := j.toRingHom.toAlgebra
  let sH₀H₁ : SMul H₀.val H₁.val := aH₀H₁.toSMul
  have hKH₀H₁ : IsScalarTower K H₀.val H₁.val :=
    IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
  have hrestriction : AlgEquiv.restrictNormalHom (F := K) (K₁ := H₁.val)
      H₀.val (σ₁.restrictScalars K) = σ₀ :=
    EtaleFundamentalGroups.finiteGaloisRestriction_eq_of_coefficient_action
      i₀ i₁ j hj τ σ₀ σ₁ hσ₀ hσ₁
  have hnorm := constantHilbertClassFieldGaloisEquivPic0_restrict_eq_norm
    v hv w hw j σ₁
  rw [hrestriction] at hnorm
  exact hnorm

end FunctionField
