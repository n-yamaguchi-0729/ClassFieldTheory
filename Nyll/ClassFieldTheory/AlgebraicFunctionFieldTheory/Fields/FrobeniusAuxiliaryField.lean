/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField

/-!
# Actual Frobenius auxiliary fields

The field and its scalar structures are constructed once for an arbitrary ambient
separable closure. Both intrinsic transport and prime-norm evaluation use this
same actual intermediate field.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The actual auxiliary field over the original base of a positive Frobenius element. -/
abbrev intrinsicFrobeniusAuxiliaryField
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    IntermediateField K Ω :=
  abstractFixedField K Ω
    ((fullConstantDegreeData k K Ω).frobeniusFixedField
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below σ)

local instance intrinsicFrobeniusAuxiliaryCommSemiring
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    CommSemiring (intrinsicFrobeniusAuxiliaryField k K Ω H T σ) :=
  (inferInstance : Field
    (intrinsicFrobeniusAuxiliaryField k K Ω H T σ)).toSemifield.toCommSemiring

local instance intrinsicFrobeniusAuxiliaryAlgebra
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    Algebra K (intrinsicFrobeniusAuxiliaryField k K Ω H T σ) :=
  (intrinsicFrobeniusAuxiliaryField k K Ω H T σ).algebra

local instance intrinsicFrobeniusAuxiliarySMul
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    SMul K (intrinsicFrobeniusAuxiliaryField k K Ω H T σ) :=
  (intrinsicFrobeniusAuxiliaryAlgebra k K Ω H T σ).toSMul

local instance intrinsicFrobeniusAuxiliaryModule
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    Module K (intrinsicFrobeniusAuxiliaryField k K Ω H T σ) :=
  (intrinsicFrobeniusAuxiliaryAlgebra k K Ω H T σ).toModule

/-- The actual auxiliary fixed field of a positive ambient Frobenius element. -/
abbrev ambientFrobeniusAuxiliaryField
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    IntermediateField (abstractFixedField K Ω H.field) Ω :=
  abstractRelativeFixedField K Ω
    ((fullConstantDegreeData k K Ω).frobeniusFixedField_le
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below σ)

local instance ambientFrobeniusAuxiliaryAlgebra
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    Algebra (abstractFixedField K Ω H.field) (ambientFrobeniusAuxiliaryField k K Ω H T σ) :=
  (ambientFrobeniusAuxiliaryField k K Ω H T σ).algebra

variable [Algebra k Ω] [IsScalarTower k K Ω]

local instance intrinsicFrobeniusAuxiliaryConstantAlgebra
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    Algebra k (intrinsicFrobeniusAuxiliaryField k K Ω H T σ) :=
  IntermediateField.algebra' (R' := k) (intrinsicFrobeniusAuxiliaryField k K Ω H T σ)

local instance ambientFrobeniusAuxiliaryConstantAlgebra
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below) :
    Algebra k (ambientFrobeniusAuxiliaryField k K Ω H T σ) :=
  IntermediateField.algebra' (R' := k) (abstractFixedField K Ω
    ((fullConstantDegreeData k K Ω).frobeniusFixedField
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below σ))

end FunctionField
