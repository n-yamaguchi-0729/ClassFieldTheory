/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusTransport
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FrobeniusNormWitness
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativePrimeNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-!
# Native reciprocity on the intrinsic Frobenius auxiliary field
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra k (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [fixedBaseRatFuncAlgebra :
      Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]

attribute [local instance]
  fixedBaseCommSemiring
  fixedBaseClosureAlgebra
  fixedBaseClosureSMul
  fixedBaseClosureModule
  relativeFixedFieldCommSemiring
  relativeFixedFieldAlgebra
  relativeFixedFieldSMul
  relativeFixedFieldModule
  fixedBaseAmbientTower
  relativeFixedFieldFiniteDimensional
  relativeFixedFieldGalois
  fixedBaseFrobeniusAuxiliaryCommSemiring
  fixedBaseFrobeniusAuxiliaryAlgebra
  fixedBaseFrobeniusAuxiliarySMul
  fixedBaseFrobeniusAuxiliaryModule
  ambientFrobeniusAuxiliaryAlgebra
  relativeFixedFieldAmbientAlgebra
  relativeFixedFieldConstantAlgebra
  relativeFixedFieldConstantTower
  fixedBasePrincipalDivisors
  relativeFixedFieldPrincipalDivisors
  fixedBaseFrobeniusAuxiliaryConstantAlgebra
  ambientFrobeniusAuxiliaryConstantAlgebra

section IntrinsicLiftValue

variable
    [Algebra k (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [Algebra (RatFunc k)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [fixedBaseClosureConstantTower :
      IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [IsScalarTower (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [IsScalarTower k (RatFunc k)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]

/-- The intrinsic norm evaluates to the Frobenius transported to the original closure. -/
theorem native_frobenius_norm_eq_ambient
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e)
    [FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ)]
    [Algebra.IsSeparable (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ)]
    [IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ)]
    [auxiliaryPrincipalDivisors :
      AlgebraicCurve.HasPrincipalDivisors k (fixedBaseFrobeniusAuxiliaryField k K H T e σ)]
    (c : IdeleClassGroup k (fixedBaseFrobeniusAuxiliaryField k K H T e σ))
    (hc : (IdeleClassGroup.normalizedDegree (k := k)
      (K := fixedBaseFrobeniusAuxiliaryField k K H T e σ) c).toAdd = 1) :
    finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below)
      (IdeleClassGroup.norm (k := k)
        (K := abstractFixedField K (SeparableClosure K) H.field)
        (L := fixedBaseFrobeniusAuxiliaryField k K H T e σ) c) =
      Abelianization.of
        (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
          H.field T.field T.below T.normal
          ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusRestriction
            (H.toFiniteResidueAbstractField
              (fullConstantDegreeData k K (SeparableClosure K))) T.field T.below
              (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))) := by
  let F : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let E : IntermediateField F (SeparableClosure K) :=
    abstractRelativeFixedField K (SeparableClosure K) T.below
  let i : E →ₐ[F] SeparableClosure F := e.symm.toAlgHom.comp E.val
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
  let qI : EI.extensionQuotient ≃* Gal(E/F) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E i
  let qA : T.extensionQuotient ≃* Gal(E/F) :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field T.field T.below T.normal
  have hEcomm : IsMulCommutative Gal(E/F) :=
    qA.surjective.isMulCommutative inferInstance
  have hEIcomm : IsMulCommutative EI.extensionQuotient :=
    qI.symm.surjective.isMulCommutative hEcomm
  have hEI : Finite EI.extensionQuotient := EI.finite
  let DI := fullConstantDegreeData k F (SeparableClosure F)
  let RI := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI
  have hn :
      finiteArtin k F E
          (IdeleClassGroup.norm (k := k) (K := F)
            (L := fixedBaseFrobeniusAuxiliaryField k K H T e σ) c) =
        Abelianization.of (qI (DI.frobeniusRestriction RI EI.field EI.below σ)) := by
    with_reducible_and_instances
      exact finiteArtin_frobenius_primeNorm_of_embedding k F E i σ c hc
  have hrestriction := intrinsicConstantFrobeniusRestriction_eq_ambientFixedField k K H T e σ
  with_reducible_and_instances
    exact hn.trans (congrArg
      (Abelianization.of : Gal(E/F) → Abelianization Gal(E/F)) hrestriction).symm

end IntrinsicLiftValue

end FunctionField
