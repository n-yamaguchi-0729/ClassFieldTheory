/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FinitePrimeNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativePresentation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization

/-!
# Native prime-norm values under actual fixed-field presentations

The concrete norm formula is evaluated in the native finite Artin map using
the actual fixed-field presentation. The Galois value uses scalar restriction
directly, so its computation does not reconstruct the degree-one equivalence.
-/

noncomputable section


namespace FunctionField

open ClassFormation LocalClassFieldTheory CyclicCohomology

attribute [local instance]
  intrinsicFrobeniusAuxiliaryCommSemiring
  intrinsicFrobeniusAuxiliaryAlgebra
  intrinsicFrobeniusAuxiliarySMul
  intrinsicFrobeniusAuxiliaryModule
  intrinsicFrobeniusAuxiliaryConstantAlgebra

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [akΩ : Algebra k (SeparableClosure K)]
    [aRΩ : Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

/-- Native reciprocity sends the actual norm of every normalized-degree-one
Frobenius auxiliary class to the automorphism of its actual field presentation. -/
theorem finiteArtin_frobenius_primeNorm_of_presentation
    (T : FiniteGaloisSubextension (intrinsicFiniteAbstractBase K).field)
    [IsMulCommutative T.extensionQuotient]
    (eE : L ≃ₐ[K] abstractFixedField K (SeparableClosure K) T.field) :
    let Ω := SeparableClosure K
    let H := intrinsicFiniteAbstractBase K
    let _ : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) := T.finite
    let D := fullConstantDegreeData k K Ω
    let R := H.toFiniteResidueAbstractField D
    ∀ σ : D.FrobeniusElements R T.field T.below,
      let S := D.frobeniusFixedField R T.field T.below σ
      let A : IntermediateField K Ω := intrinsicFrobeniusAuxiliaryField k K Ω H T σ
      let hSfinite := D.frobeniusFixedField_absoluteFinite H T.field T.below σ
      let _ : FiniteDimensional K A :=
        abstractFixedField_finiteDimensional K Ω S hSfinite
      ∀ c : IdeleClassGroup k A,
        (IdeleClassGroup.normalizedDegree (k := k) (K := A) c).toAdd = 1 →
        finiteArtin k K L
            (IdeleClassGroup.norm (k := k) (K := K) (L := A) c) =
          Abelianization.of ((AlgEquiv.autCongr eE).symm
            ((abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
              (D.frobeniusRestriction R T.field T.below σ)).restrictScalars K)) := by
  intro Ω H
  have nativeEvaluation := finiteArtin_eq_fixedFieldPresentation
    (akΩ := akΩ) (aRΩ := aRΩ) k K L T eE
  intro hTfinite D R σ S A hSfinite hKS c hc
  let eF := finiteGaloisBaseFixedFieldEquiv K
  let b := IdeleClassGroup.norm (k := k) (K := K) (L := A) c
  have hp := normQuotientEquivOfFixedFieldPresentation_primeNorm
    k K L Ω H T eF eE σ c hc
  -- Native reciprocity names its separable closure and base presentation concretely.
  -- Normalize just these aliases once before comparing the dependent norm types.
  dsimp only [Ω, H, eF] at hp
  have hn := nativeEvaluation b
  refine hn.trans ?_
  exact hp


/-- For a specified embedding, the prime-norm formula gives the corresponding
concrete finite Galois quotient action. The fixed-field presentation is built
and compared over the original base before any specialization of that base. -/
theorem finiteArtin_frobenius_primeNorm_of_embedding
    (i : L →ₐ[K] SeparableClosure K)
    [IsMulCommutative (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient] :
    let H := intrinsicFiniteAbstractBase K
    let T := finiteGaloisAbstractExtensionOfEmbedding K L i
    let _ : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) := T.finite
    let D := fullConstantDegreeData k K (SeparableClosure K)
    let R := H.toFiniteResidueAbstractField D
    ∀ σ : D.FrobeniusElements R T.field T.below,
      let S := D.frobeniusFixedField R T.field T.below σ
      let A : IntermediateField K (SeparableClosure K) :=
        intrinsicFrobeniusAuxiliaryField k K (SeparableClosure K) H T σ
      let hSfinite := D.frobeniusFixedField_absoluteFinite H T.field T.below σ
      let _ : FiniteDimensional K A :=
        abstractFixedField_finiteDimensional K (SeparableClosure K) S hSfinite
      ∀ c : IdeleClassGroup k A,
        (IdeleClassGroup.normalizedDegree (k := k) (K := A) c).toAdd = 1 →
        finiteArtin k K L
            (IdeleClassGroup.norm (k := k) (K := K) (L := A) c) =
          Abelianization.of (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
            (D.frobeniusRestriction R T.field T.below σ)) := by
  intro H T hTfinite
  let eE := finiteGaloisEmbeddedFixedFieldEquiv K L i
  have presentationValue := finiteArtin_frobenius_primeNorm_of_presentation k K L T eE
  have quotientAction := presentedGaloisQuotientOfEmbedding K L i
  intro D R σ S A hSfinite hKS c hc
  have hp := presentationValue σ c hc
  have hq := quotientAction (D.frobeniusRestriction R T.field T.below σ)
  exact hp.trans (congrArg Abelianization.of hq)

end FunctionField
