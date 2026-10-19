/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.IntrinsicFrobeniusTransport
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-!
# Surjectivity of intrinsic Frobenius transport
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
  relativeFixedFieldFiniteDimensional
  relativeFixedFieldGalois

omit [Algebra (RatFunc k) (SeparableClosure K)]
  [IsScalarTower (RatFunc k) K (SeparableClosure K)]
  [IsScalarTower k (RatFunc k) (SeparableClosure K)] in
/-- Every positive ambient Frobenius element lifts to the intrinsic fixed-base presentation. -/
theorem intrinsicFrobeniusToAmbient_surjective
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K) :
    Function.Surjective
      (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e) := by
  let F : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) H.field
  let E : IntermediateField F (SeparableClosure K) :=
    abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  let DI := fullConstantDegreeData k F (SeparableClosure F)
  let RI := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI
  let DA := fullConstantDegreeData k K (SeparableClosure K)
  let RA := H.toFiniteResidueAbstractField DA
  have hEI_normal : (extensionSubgroup RI.field EI.field EI.below).Normal := EI.normal
  let ξ := intrinsicConstantFrobeniusQuotientEquivAmbientFixedField k K H T e
  intro σA
  have hξ := ξ.apply_symm_apply σA.val
  have hdegree := intrinsicConstantFrobeniusQuotientEquivAmbientFixedField_degree
    k K H T e (ξ.symm σA.val)
  have hvalue := hdegree.symm.trans
    (congrArg (DA.extensionNormalizedDegree RA T.field T.below) hξ)
  have hpositive : ∃ n : ℕ, 0 < n ∧
      DI.extensionNormalizedDegree RI EI.field EI.below (ξ.symm σA.val) =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    rw [hvalue]
    exact σA.property
  let σ : DI.FrobeniusElements RI EI.field EI.below := ⟨ξ.symm σA.val, hpositive⟩
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact hξ

end FunctionField
