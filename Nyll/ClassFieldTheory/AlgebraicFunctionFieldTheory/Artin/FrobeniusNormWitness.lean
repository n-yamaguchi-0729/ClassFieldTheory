/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOneNormWitness
public import Nyll.ClassFieldTheory.Algebra.FiniteAbstractFixedField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Common degree-one norms for the actual Frobenius auxiliary fields

The existing closure equivalence restricts to the two actual auxiliary fields.
Transport of a degree-one idele class along this constructed field equivalence
gives degree-one classes whose real norms to the fixed base coincide.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

/-- The constant-field action is compatible with the relative fixed-field tower. -/
theorem relativeFixedField_constantTower
    (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (H S : ClosedSubgroup Gal(Ω/K)) (hSH : S.toSubgroup ≤ H.toSubgroup) :
    have _ : IsScalarTower k (abstractFixedField K Ω H) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H) Ω
    IsScalarTower k (abstractFixedField K Ω H) (abstractRelativeFixedField K Ω hSH) := by
  intro hkFΩ
  exact IsScalarTower.of_algebraMap_eq
    (R := k) (S := abstractFixedField K Ω H) (A := abstractRelativeFixedField K Ω hSH)
    (fun _ => Subtype.ext rfl)

/-- The Frobenius fixed field is finite-dimensional over the original base field. -/
theorem frobeniusFixedField_finiteDimensional
    (F : Type v) (Ω : Type w) [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (D : DegreeData Gal(Ω/F)) (H : FiniteAbstractField Gal(Ω/F))
    (T : FiniteGaloisSubextension H.field) :
    let HR := H.toFiniteResidueAbstractField D
    let _ : (extensionSubgroup HR.field T.field T.below).Normal := T.normal
    ∀ σ : D.FrobeniusElements HR T.field T.below,
      let S : IntermediateField F Ω := abstractFixedField F Ω
        (D.frobeniusFixedField HR T.field T.below σ)
      let _ : CommSemiring S := (inferInstance : Field S).toSemifield.toCommSemiring
      let aFS : Algebra F S := S.algebra
      let _ : Module F S := aFS.toModule
      FiniteDimensional F S := by
  intro HR hTnormal σ S cS aFS mFS
  have hTfinite : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) :=
    T.finite
  exact abstractFixedField_finiteDimensional F Ω
    (D.frobeniusFixedField HR T.field T.below σ)
    (D.frobeniusFixedField_absoluteFinite H T.field T.below σ)

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
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

end CommonNormWitness

end FunctionField
