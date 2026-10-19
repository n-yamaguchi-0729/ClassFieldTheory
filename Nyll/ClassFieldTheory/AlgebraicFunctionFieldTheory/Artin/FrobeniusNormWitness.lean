/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusTransport
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOneNormWitness
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-!
# Common degree-one norms for the actual Frobenius auxiliary fields

The existing closure equivalence restricts to the two actual auxiliary fields.
Transport of a degree-one idele class along this constructed field equivalence
gives degree-one classes whose real norms to the fixed base coincide.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

private theorem relativeFixedField_constantTower
    (k K Ω : Type) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (H S : ClosedSubgroup Gal(Ω/K)) (hSH : S.toSubgroup ≤ H.toSubgroup) :
    have _ : IsScalarTower k (abstractFixedField K Ω H) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H) Ω
    IsScalarTower k (abstractFixedField K Ω H) (abstractRelativeFixedField K Ω hSH) := by
  intro hkFΩ
  exact IsScalarTower.of_algebraMap_eq
    (R := k) (S := abstractFixedField K Ω H) (A := abstractRelativeFixedField K Ω hSH)
    (fun _ => Subtype.ext rfl)

private theorem frobeniusFixedField_finiteDimensional
    (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (D : DegreeData Gal(Ω/F)) (H : FiniteAbstractField Gal(Ω/F))
    (T : FiniteGaloisSubextension H.field)
    (σ : D.FrobeniusElements (H.toFiniteResidueAbstractField D) T.field T.below) :
    let S : IntermediateField F Ω := abstractFixedField F Ω
      (D.frobeniusFixedField (H.toFiniteResidueAbstractField D) T.field T.below σ)
    let _ : CommSemiring S := (inferInstance : Field S).toSemifield.toCommSemiring
    let aFS : Algebra F S := S.algebra
    let _ : Module F S := aFS.toModule
    FiniteDimensional F S := by
  intro S cS aFS mFS
  have hTfinite : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) :=
    T.finite
  exact abstractFixedField_finiteDimensional F Ω
    (D.frobeniusFixedField (H.toFiniteResidueAbstractField D) T.field T.below σ)
    (D.frobeniusFixedField_absoluteFinite H T.field T.below σ)

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

-- The original ambient field supplies the small-base and constant structures.
-- Only the relative-base action is taken from the relative fixed field.
local instance relativeFixedFieldAmbientAlgebra (T : FiniteGaloisSubextension H.field) :
    Algebra K (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  (abstractFixedField K (SeparableClosure K) T.field).algebra

local instance relativeFixedFieldConstantAlgebra (T : FiniteGaloisSubextension H.field) :
    Algebra k (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  IntermediateField.algebra' (R' := k) (abstractFixedField K (SeparableClosure K) T.field)

local instance relativeFixedFieldConstantTower (T : FiniteGaloisSubextension H.field) :
    IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  relativeFixedField_constantTower k K (SeparableClosure K) H.field T.field T.below

local instance fixedBasePrincipalDivisors :
    AlgebraicCurve.HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) H.field) :=
  (isCurveOver k (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors

local instance relativeFixedFieldPrincipalDivisors (T : FiniteGaloisSubextension H.field) :
    AlgebraicCurve.HasPrincipalDivisors k (abstractRelativeFixedField K
      (SeparableClosure K) T.below) :=
  (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k
    (abstractFixedField K (SeparableClosure K) H.field)
    (abstractRelativeFixedField K (SeparableClosure K) T.below)).toHasPrincipalDivisors

section CommonNormWitness

variable
    [Algebra k (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
    [IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]

local instance fixedBaseFrobeniusAuxiliaryConstantAlgebra
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    Algebra k (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliaryConstantAlgebra
    k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

attribute [local instance]
  fixedBaseFrobeniusAuxiliaryConstantAlgebra
  ambientFrobeniusAuxiliaryConstantAlgebra

omit [Algebra (RatFunc k) (SeparableClosure K)]
  [IsScalarTower (RatFunc k) K (SeparableClosure K)]
  [IsScalarTower k (RatFunc k) (SeparableClosure K)] in
/-- The actual intrinsic and ambient auxiliary fields share a degree-one norm. -/
theorem exists_common_frobenius_norm
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    have φ : (fixedBaseFrobeniusAuxiliaryField k K H T e σ)
        ≃ₐ[abstractFixedField K (SeparableClosure K) H.field]
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) :=
      intrinsicConstantFrobeniusFixedFieldEquivAmbientFixedField k K H T e σ
    have _ :
    IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
      IsScalarTower.of_algebraMap_eq
        (R := k) (S := abstractFixedField K (SeparableClosure K) H.field)
        (A := fixedBaseFrobeniusAuxiliaryField k K H T e σ)
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k
          (abstractFixedField K (SeparableClosure K) H.field)
          (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)) x))
    have _ :
    IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) :=
      relativeFixedField_constantTower k K (SeparableClosure K) H.field
        ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusFixedField
          (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
          T.field T.below
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))
        ((fullConstantDegreeData k K (SeparableClosure K)).frobeniusFixedField_le
          (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
          T.field T.below
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))
    have _ :
    FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
        (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
      frobeniusFixedField_finiteDimensional
        (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))
        (fullConstantDegreeData k (abstractFixedField K (SeparableClosure K) H.field)
          (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)))
        (intrinsicFiniteAbstractBase (abstractFixedField K (SeparableClosure K) H.field))
        (finiteGaloisAbstractExtensionOfEmbedding
          (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K) T.below)
          (e.symm.toAlgHom.comp (abstractRelativeFixedField K (SeparableClosure K) T.below).val)) σ
    have _ :
    Algebra.IsSeparable (abstractFixedField K (SeparableClosure K) H.field)
        (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
      IntermediateField.isSeparable_tower_bot
        (abstractFixedField K (SeparableClosure K) H.field)
        (K := SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))
        (fixedBaseFrobeniusAuxiliaryField k K H T e σ)
    have _ :
    FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) :=
      φ.toLinearEquiv.finiteDimensional
    have _ :
    Algebra.IsSeparable (abstractFixedField K (SeparableClosure K) H.field)
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) :=
      AlgEquiv.Algebra.isSeparable φ
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) H.field) :=
      (isCurveOver k (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    have _ :
    AlgebraicCurve.HasPrincipalDivisors k (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k
        (abstractFixedField K (SeparableClosure K) H.field)
        (fixedBaseFrobeniusAuxiliaryField k K H T e σ)).toHasPrincipalDivisors
    have _ :
    AlgebraicCurve.HasPrincipalDivisors k
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k
        (abstractFixedField K (SeparableClosure K) H.field)
        (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))
        ).toHasPrincipalDivisors
    ∃ (cI : IdeleClassGroup k (fixedBaseFrobeniusAuxiliaryField k K H T e σ))
      (cA : IdeleClassGroup k (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ))),
      (IdeleClassGroup.normalizedDegree (k := k)
        (K := fixedBaseFrobeniusAuxiliaryField k K H T e σ) cI).toAdd = 1 ∧
      (IdeleClassGroup.normalizedDegree (k := k)
        (K := ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) cA).toAdd = 1 ∧
      IdeleClassGroup.norm (k := k)
          (K := abstractFixedField K (SeparableClosure K) H.field)
          (L := fixedBaseFrobeniusAuxiliaryField k K H T e σ) cI =
        IdeleClassGroup.norm (k := k)
          (K := abstractFixedField K (SeparableClosure K) H.field)
          (L := ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) cA := by
  intro φ hkFLI hkFLA hFLI hLIsep hFLA hLAsep hFprincipal hLIprincipal hLAprincipal
  with_reducible
    exact IdeleClassGroup.exists_normalizedDegree_one_norm_eq_of_algEquiv k
      (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ)
      (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
          (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) φ

end CommonNormWitness

end FunctionField
