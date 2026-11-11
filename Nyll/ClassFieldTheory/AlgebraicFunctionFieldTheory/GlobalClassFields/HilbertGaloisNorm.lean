/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ConstantHilbertNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Galois restriction and the actual constant-stage Picard norm

For an actual embedding between two pointed Hilbert fields, restriction of
the original Galois automorphism corresponds to the original Picard norm.
The equality is deduced from finite global norm reciprocity, using the
proved degree-zero idele representative of the upper automorphism.
The theorem does not assert existence of a Hilbert-field embedding.
-/

@[expose] public section

noncomputable section

universe u v w x y

open AlgebraicCurve

namespace FunctionField

variable {k : Type u} {C : Type v} {E : Type w} {K : Type x} {L : Type y}
    [Field k] [Finite k] [Field C] [Field E]
    [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra k C] [Algebra C K] [IsScalarTower k C K] [Module.Finite k C]
    [Algebra k E] [Algebra E L] [IsScalarTower k E L] [Algebra.IsIntegral k E]
    [Algebra C E] [IsScalarTower k C E] [Algebra.IsIntegral C E]
    [Algebra C L] [IsScalarTower k C L] [IsScalarTower C E L] [IsScalarTower C K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [HasPrincipalDivisors C K] [HasPrincipalDivisors C L] [HasPrincipalDivisors E L]

omit [IsScalarTower k C E] in
/-- Literal Galois restriction through a specified Hilbert-field embedding
is the actual norm on Picard classes at the two constant stages. No
compatibility of chosen idele representatives is assumed. -/
theorem constantHilbertClassFieldGaloisEquivPic0_restrict_eq_norm
    (ε : Place C K) (hε : ε.deg = 1) (η : Place E L) (hη : η.deg = 1) :
    let H₀ := hilbertClassField k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    let H₁ := hilbertClassField k L {η.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    let _ : Algebra K H₁.val :=
      ((algebraMap L H₁.val).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L H₁.val :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ i : H₀.val →ₐ[K] H₁.val,
      let aH₀H₁ : Algebra H₀.val H₁.val := i.toRingHom.toAlgebra
      let _ : SMul H₀.val H₁.val := aH₀H₁.toSMul
      let _ : IsScalarTower K H₀.val H₁.val :=
        IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
      ∀ σ : Gal(H₁.val/L),
        H1Gm.ofPic0 C K
            ((constantHilbertClassFieldGaloisEquivPic0 k C K ε hε)
              (AlgEquiv.restrictNormalHom (F := K) (K₁ := H₁.val)
                H₀.val (σ.restrictScalars K))).toAdd =
          Pic.normConstants C E K L
            (H1Gm.ofPic0 E L
              ((constantHilbertClassFieldGaloisEquivPic0 k E L η hη) σ).toAdd) := by
  intro H₀ H₁ aKH₁ hKLH₁ i aH₀H₁ sH₀H₁ hKH₀H₁ σ
  let aKS : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRKS : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKS : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKS : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRKS : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
  let aLS : Algebra k (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap k L)).toAlgebra
  let aRLS : Algebra (RatFunc k) (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap (RatFunc k) L)).toAlgebra
  have hkLS : IsScalarTower k L (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRLS : IsScalarTower (RatFunc k) L (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRLS : IsScalarTower k (RatFunc k) (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap L (SeparableClosure L))
        (IsScalarTower.algebraMap_apply k (RatFunc k) L a))
  have hkKH₁ : IsScalarTower k K H₁.val :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply k L H₁.val]
      exact congrArg (algebraMap L H₁.val) (IsScalarTower.algebraMap_apply k K L a))
  have hkH₀H₁ : IsScalarTower k H₀.val H₁.val :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply k K H₀.val,
        IsScalarTower.algebraMap_apply k K H₁.val]
      exact (i.commutes (algebraMap k K a)).symm)
  have hpH₀ : HasPrincipalDivisors k H₀.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H₀.val).toHasPrincipalDivisors
  have hpH₁ : HasPrincipalDivisors k H₁.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k L H₁.val).toHasPrincipalDivisors
  obtain ⟨c, hc, hdegree⟩ := exists_zeroDegree_ideleClass_artin k E L η hη σ
  have hrestriction :
      AlgEquiv.restrictNormalHom (F := K) (K₁ := H₁.val)
        H₀.val (σ.restrictScalars K) =
        abelianFiniteArtin k K H₀.val
          (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L) c) := by
    rw [← hc]
    exact abelianFiniteArtin_finiteNorm_restrictNormal
      (k := k) (K := K) (F := L) (L := H₀.val) (M := H₁.val) c
  rw [hrestriction, constantHilbertClassFieldGaloisEquivPic0_artin]
  exact IdeleClassGroup.ofPic0_constantPointedDivisorClass_eq_normConstants
    ε hε c ((constantHilbertClassFieldGaloisEquivPic0 k E L η hη) σ).toAdd hdegree

end FunctionField
