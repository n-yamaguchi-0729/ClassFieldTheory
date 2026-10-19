/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldPrimeNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusTransport
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FrobeniusNormWitness
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeFrobeniusEvaluation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusSurjectivity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import
  Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-!
# Native reciprocity over an actual fixed base field

The common norm witnesses are supplied by the actual auxiliary-field construction.
The two existing prime norm evaluations then determine reciprocity on all classes.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra k (SeparableClosure K)]
    [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]
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
    [IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [IsScalarTower (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [IsScalarTower k (RatFunc k)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]

private theorem exists_common_frobenius_value_of_intrinsicLift
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    ∃ c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field),
      fixedFieldArtin k K (SeparableClosure K) H T c = Abelianization.of
        (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
          H.field T.field T.below T.normal
          ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusRestriction
            (H.toFiniteResidueAbstractField
              (fullConstantDegreeData k K (SeparableClosure K))) T.field T.below
              (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))) ∧
      finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractRelativeFixedField K (SeparableClosure K) T.below) c =
          fixedFieldArtin k K (SeparableClosure K) H T c := by
  let ambient := fixedFieldArtin k K (SeparableClosure K) H T
  have ambientPrimeValue := fixedFieldArtin_frobenius_primeNorm
    k K (SeparableClosure K) H T
  let σA := intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ
  have hWitness := exists_common_frobenius_norm k K H T e σ
  extract_lets (config := { descend := false, merge := false }) at hWitness
  dsimp (config := { instances := true, zetaDelta := false }) only
    [fixedBaseFrobeniusAuxiliaryAlgebra, fixedBaseFrobeniusAuxiliaryConstantAlgebra,
      fixedBaseFrobeniusAuxiliaryCommSemiring, fixedBaseFrobeniusAuxiliarySMul,
      fixedBaseFrobeniusAuxiliaryModule, fixedBaseFrobeniusAuxiliaryField,
      fixedBaseClosureAlgebra, fixedBaseClosureSMul, fixedBaseClosureModule] at hWitness
  obtain ⟨cI, cA, hcI, hcA, hnorm⟩ := hWitness
  let b : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field) :=
    IdeleClassGroup.norm (k := k)
      (K := abstractFixedField K (SeparableClosure K) H.field)
      (L := fixedBaseFrobeniusAuxiliaryField k K H T e σ) cI
  have hn := native_frobenius_norm_eq_ambient k K H T e σ cI hcI
  have ambientAtLift := ambientPrimeValue σA
  have hA := ambientAtLift cA hcA
  refine ⟨b, ?_, ?_⟩
  · exact (congrArg ambient hnorm).trans hA
  · exact hn.trans ((congrArg ambient hnorm).trans hA).symm

end IntrinsicLiftValue

private theorem exists_common_frobenius_value_of_lift
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (σA₀ : (fullConstantDegreeData k K (SeparableClosure K)).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
      T.field T.below) :
    ∃ c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field),
      fixedFieldArtin k K (SeparableClosure K) H T c = Abelianization.of
        (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
          H.field T.field T.below T.normal
          ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusRestriction
            (H.toFiniteResidueAbstractField
              (fullConstantDegreeData k K (SeparableClosure K))) T.field T.below σA₀)) ∧
      finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractRelativeFixedField K (SeparableClosure K) T.below) c =
          fixedFieldArtin k K (SeparableClosure K) H T c := by
  let F : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let akFS : Algebra k (SeparableClosure F) :=
    ((fixedBaseClosureAlgebra (K := K) (H := H)).algebraMap.comp
      (algebraMap k F)).toAlgebra
  let skFS : SMul k (SeparableClosure F) := akFS.toSMul
  let mkFS : Module k (SeparableClosure F) := akFS.toModule
  let aRFS : Algebra (RatFunc k) (SeparableClosure F) :=
    ((fixedBaseClosureAlgebra (K := K) (H := H)).algebraMap.comp
      fixedBaseRatFuncAlgebra.algebraMap).toAlgebra
  have hkFS : IsScalarTower k F (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRFS : IsScalarTower (RatFunc k) F (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRFS : IsScalarTower k (RatFunc k) (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap F (SeparableClosure F))
      (IsScalarTower.algebraMap_apply k (RatFunc k) F x))
  have hsepFA : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
  have hclosure : IsSepClosure F (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let e : SeparableClosure F ≃ₐ[F] SeparableClosure K :=
    IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  have hLift := intrinsicFrobeniusToAmbient_surjective k K H T e σA₀
  let σ : intrinsicFixedBaseFrobeniusElements k K H T e := Classical.choose hLift
  have hσA :
      intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ = σA₀ :=
    Classical.choose_spec hLift
  have hCommon := exists_common_frobenius_value_of_intrinsicLift k K H T e σ
  let b := Classical.choose hCommon
  have hb := Classical.choose_spec hCommon
  have htarget := congrArg
    (fun σA : (fullConstantDegreeData k K (SeparableClosure K)).FrobeniusElements
        (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
        T.field T.below =>
      Abelianization.of
        (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
          H.field T.field T.below T.normal
          ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusRestriction
            (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
            T.field T.below σA))) hσA
  exact ⟨b, hb.1.trans htarget, hb.2⟩

private theorem exists_common_frobenius_value
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (τ : Gal((abstractRelativeFixedField K
      (SeparableClosure K) T.below)/(abstractFixedField K (SeparableClosure K) H.field))) :
    ∃ c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field),
      finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractRelativeFixedField K (SeparableClosure K) T.below) c = Abelianization.of τ ∧
      fixedFieldArtin k K (SeparableClosure K) H T c = Abelianization.of τ := by
  let F : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let E : IntermediateField F (SeparableClosure K) :=
    abstractRelativeFixedField K (SeparableClosure K) T.below
  let DA := fullConstantDegreeData k K (SeparableClosure K)
  let RA := H.toFiniteResidueAbstractField DA
  let qA : T.extensionQuotient ≃* Gal(E/F) :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field T.field T.below T.normal
  have hTfinite : Finite (H.field.toSubgroup ⧸
      extensionSubgroup H.field T.field T.below) := T.finite
  have hsurjective : Function.Surjective
      (fun σA : DA.FrobeniusElements RA T.field T.below =>
        qA (DA.frobeniusRestriction RA T.field T.below σA)) :=
    qA.surjective.comp (DA.frobeniusRestriction_surjective RA T.field T.below)
  have hLift := hsurjective τ
  let σA := Classical.choose hLift
  have hστ := Classical.choose_spec hLift
  have hCommon := exists_common_frobenius_value_of_lift k K H T σA
  let b := Classical.choose hCommon
  have hb := Classical.choose_spec hCommon
  have htarget := congrArg Abelianization.of hστ
  exact ⟨b, hb.2.trans (hb.1.trans htarget), hb.1.trans htarget⟩

/-- Native reciprocity over a finite fixed base agrees with the reciprocity
constructed in the original ambient separable closure. -/
theorem finiteArtin_eq_fixedFieldArtin
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field)) :
    finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) c =
        fixedFieldArtin k K (SeparableClosure K) H T c := by
  let native : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field) →*
      Abelianization Gal((abstractRelativeFixedField K (SeparableClosure K) T.below)/
        (abstractFixedField K (SeparableClosure K) H.field)) :=
    finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below)
  let ambient : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field) →*
      Abelianization Gal((abstractRelativeFixedField K (SeparableClosure K) T.below)/
        (abstractFixedField K (SeparableClosure K) H.field)) :=
    fixedFieldArtin k K (SeparableClosure K) H T
  change native c = ambient c
  have nativeKernel := finiteArtin_eq_one_iff_mem_norm k
    (abstractFixedField K (SeparableClosure K) H.field)
    (abstractRelativeFixedField K (SeparableClosure K) T.below)
  have ambientKernel := fixedFieldArtin_eq_one_iff_mem_norm k K (SeparableClosure K) H T
  let F : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let E : IntermediateField F (SeparableClosure K) :=
    abstractRelativeFixedField K (SeparableClosure K) T.below
  have hRepresentative := (show Function.Surjective
    (Abelianization.of : Gal(E/F) →* Abelianization Gal(E/F)) from
      QuotientGroup.mk_surjective) (native c)
  let τ : Gal(E/F) := Classical.choose hRepresentative
  have hτ := Classical.choose_spec hRepresentative
  have hCommon := exists_common_frobenius_value k K H T τ
  let b : IdeleClassGroup k F := Classical.choose hCommon
  have hbNative := (Classical.choose_spec hCommon).1
  have hbAmbient := (Classical.choose_spec hCommon).2
  have hbc : native b = native c := hbNative.trans hτ
  have hN : native (c / b) = 1 :=
    (map_div native c b).trans
      ((congrArg (fun z => native c / z) hbc).trans (div_self' (native c)))
  have hmem := (nativeKernel (c / b)).mp hN
  have hA : ambient (c / b) = 1 := (ambientKernel (c / b)).mpr hmem
  have hAcb : ambient c = ambient b :=
    eq_of_div_eq_one ((map_div ambient c b).symm.trans hA)
  exact hτ.symm.trans (hbAmbient.symm.trans hAcb.symm)

end FunctionField
