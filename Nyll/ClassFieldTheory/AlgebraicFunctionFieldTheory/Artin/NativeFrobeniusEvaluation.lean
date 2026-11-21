/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeFrobeniusNorm

/-!
# Common Frobenius value on the original fixed base
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k : Type u) (K : Type v) [kField : Field k] [kFinite : Finite k] [KField : Field K]
    [kK : Algebra k K] [kRatK : Algebra (RatFunc k) K] [kRatKTower : IsScalarTower k (RatFunc k) K]
    [kFunctionField : FunctionField k K] [kClosure : Algebra k (SeparableClosure K)]
    [kClosureTower : IsScalarTower k K (SeparableClosure K)]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [fixedBaseRatFuncAlgebra :
      Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [fixedBaseRatFuncTower :
      IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [fixedBaseFunctionField : FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]

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

attribute [local instance] nativeFrobeniusExtensionNormal

section IntrinsicLiftValue

variable
    [intrinsicClosureAlgebra :
      Algebra k (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [intrinsicClosureRatFuncAlgebra :
      Algebra (RatFunc k) (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [fixedBaseClosureConstantTower :
      IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [intrinsicClosureRatFuncTower :
      IsScalarTower (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [intrinsicClosureConstantRatFuncTower :
      IsScalarTower k (RatFunc k)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]


variable
    [ambientClosureRatFuncAlgebra : Algebra (RatFunc k) (SeparableClosure K)]
    [ambientClosureRatFuncTower : IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [ambientClosureConstantRatFuncTower : IsScalarTower k (RatFunc k) (SeparableClosure K)]

omit kRatK kRatKTower kFunctionField intrinsicClosureRatFuncAlgebra intrinsicClosureRatFuncTower
    intrinsicClosureConstantRatFuncTower ambientClosureRatFuncAlgebra ambientClosureRatFuncTower
    ambientClosureConstantRatFuncTower in
private theorem intrinsicFrobeniusAuxiliaryProperties
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let LI := fixedBaseFrobeniusAuxiliaryField k K H T e σ
    IsScalarTower k F LI ∧ FiniteDimensional F LI ∧ Algebra.IsSeparable F LI := by
  intro F LI
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let TI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  have ht : IsScalarTower k F LI := IsScalarTower.of_algebraMap_eq
    (R := k) (S := F) (A := LI)
    (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k F (SeparableClosure F) x))
  have hf : FiniteDimensional F LI :=
    frobeniusFixedField_finiteDimensional F (SeparableClosure F)
      (fullConstantDegreeData k F (SeparableClosure F)) (intrinsicFiniteAbstractBase F) TI σ
  exact ⟨ht, hf, IntermediateField.isSeparable_tower_bot F (K := SeparableClosure F) LI⟩

/-- An actual degree-one norm supplies the same Frobenius value in the two
finite reciprocity maps on the fixed base. -/
theorem exists_common_frobenius_value_of_intrinsicLift
    (T : FiniteGaloisSubextension H.field) [IsMulCommutative T.extensionQuotient]
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let σA := intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ
    let ambient := fixedFieldArtin k K (SeparableClosure K) H T
    let native := finiteArtin k F (abstractRelativeFixedField K (SeparableClosure K) T.below)
    let z := Group.Abelianization.of
      (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
        H.field T.field T.below T.normal
        ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusRestriction
          (H.toFiniteResidueAbstractField
            (fullConstantDegreeData k K (SeparableClosure K))) T.field T.below σA))
    ∃ c : IdeleClassGroup k F, ambient c = z ∧ native c = ambient c := by
  intro F σA ambient native z
  let D := fullConstantDegreeData k K (SeparableClosure K)
  let HR := H.toFiniteResidueAbstractField D
  let : (extensionSubgroup HR.field T.field T.below).Normal := T.normal
  let LI := fixedBaseFrobeniusAuxiliaryField k K H T e σ
  let LA := ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T σA
  let φ : LI ≃ₐ[F] LA := intrinsicConstantFrobeniusFixedFieldEquivAmbientFixedField k K H T e σ
  have hI := intrinsicFrobeniusAuxiliaryProperties k K H T e σ
  let towerI : IsScalarTower k F LI := hI.1
  let finiteI : FiniteDimensional F LI := hI.2.1
  let sepI : Algebra.IsSeparable F LI := hI.2.2
  let towerA : IsScalarTower k F LA :=
    relativeFixedField_constantTower k K (SeparableClosure K) H.field
      (D.frobeniusFixedField HR T.field T.below σA)
      (D.frobeniusFixedField_le HR T.field T.below σA)
  let : FiniteDimensional F LA := φ.toLinearEquiv.finiteDimensional
  let : Algebra.IsSeparable F LA := AlgEquiv.Algebra.isSeparable φ
  let principalI : AlgebraicCurve.HasPrincipalDivisors k LI :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k F LI).toHasPrincipalDivisors
  let : AlgebraicCurve.HasPrincipalDivisors k LA :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k F LA).toHasPrincipalDivisors
  let fieldF : Field F := inferInstance
  let fieldI : Field LI := inferInstance
  let fieldA : Field LA := inferInstance
  let algkF : Algebra k F := inferInstance
  let algkI : Algebra k LI := fixedBaseFrobeniusAuxiliaryConstantAlgebra k K H T e σ
  let algkA : Algebra k LA := inferInstance
  let algFI : Algebra F LI := inferInstance
  let algFA : Algebra F LA := inferInstance
  let hW := @IdeleClassGroup.exists_normalizedDegree_one_norm_eq_of_algEquiv k F LI LA
    ‹Field k› ‹Finite k› fieldF fieldI fieldA algkF algkI algkA algFI algFA towerI towerA
    ‹Algebra (RatFunc k) F› ‹IsScalarTower k (RatFunc k) F› ‹FunctionField k F› finiteI sepI φ
  obtain ⟨cI, cA, hDegI, hDegA, hNorm⟩ := hW
  let nativeEval := @native_frobenius_norm_eq_ambient k K kField kFinite KField kK
    kRatK kRatKTower kFunctionField kClosure kClosureTower H
    fixedBaseRatFuncAlgebra fixedBaseRatFuncTower fixedBaseFunctionField
    intrinsicClosureAlgebra intrinsicClosureRatFuncAlgebra fixedBaseClosureConstantTower
    intrinsicClosureRatFuncTower intrinsicClosureConstantRatFuncTower
    T ‹IsMulCommutative T.extensionQuotient› e σ finiteI sepI towerI principalI
  have hNative := nativeEval cI hDegI
  let Ω := SeparableClosure K
  let fieldΩ : Field Ω := inferInstance
  let algebraΩ : Algebra K Ω := inferInstance
  let galoisΩ : IsGalois K Ω := inferInstance
  let closedΩ : IsSepClosed Ω := inferInstance
  let ambientEval := @fixedFieldArtin_frobenius_primeNorm k K Ω kField kFinite KField fieldΩ
    kK kRatK kRatKTower kFunctionField algebraΩ kClosure ambientClosureRatFuncAlgebra
    kClosureTower ambientClosureRatFuncTower ambientClosureConstantRatFuncTower galoisΩ closedΩ
    H T ‹IsMulCommutative T.extensionQuotient› σA
  have hA := ambientEval cA hDegA
  let principalF : AlgebraicCurve.HasPrincipalDivisors k F :=
    (isCurveOver k F).toHasPrincipalDivisors
  let x := (@IdeleClassGroup.norm k F LI kField fieldF fieldI
    algkF algkI algFI towerI finiteI sepI principalI principalF) cI
  let y := (IdeleClassGroup.norm (k := k) (K := F) (L := LA)) cA
  have hxy : x = y := hNorm
  have hx : native x = z := by
    with_reducible_and_instances exact hNative
  have hy : ambient y = z := by
    with_reducible_and_instances exact hA
  have hz : ambient x = z := (congrArg (fun t : IdeleClassGroup k F => ambient t) hxy).trans hy
  exact ⟨x, hz, hx.trans hz.symm⟩


end IntrinsicLiftValue

end FunctionField
