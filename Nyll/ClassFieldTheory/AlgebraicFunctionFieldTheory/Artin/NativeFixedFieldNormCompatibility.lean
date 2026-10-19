/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeFixedFieldNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldBaseCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Native norm reciprocity on actual finite fixed fields

The native symbol over the upper base is identified with the ambient symbol.
The already proved lower norm formula then gives native norm restriction.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

/-- Norm compatibility for the native symbols of actual finite normal fixed fields. -/
theorem finiteArtin_norm_restrictScalars_of_fixedField
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field)
    [Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]
    [H.field.toSubgroup.Normal] [T.field.toSubgroup.Normal]
    [IsMulCommutative T.extensionQuotient] :
    let _ : CommSemiring (abstractFixedField K (SeparableClosure K) T.field) :=
      (inferInstance : Field (abstractFixedField K (SeparableClosure K) T.field)).toSemifield
        |>.toCommSemiring
    let aKE : Algebra K (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := K)
        (abstractFixedField K (SeparableClosure K) T.field)
    let _ : SMul K (abstractFixedField K (SeparableClosure K) T.field) := aKE.toSMul
    let _ : Algebra k (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := k)
        (abstractFixedField K (SeparableClosure K) T.field)
    let aFE : Algebra (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (abstractRelativeFixedField K (SeparableClosure K) T.below).algebra
    let _ : SMul (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toSMul
    let _ : Module (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toModule
    have _ : IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure K) :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure K)
    have _ : IsScalarTower K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) T.field
        T.toFiniteAbstractFieldExtension.field.finite
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) H.field) :=
      IsGalois.of_fixedField_normal_subgroup H.field.toSubgroup
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
    have _ : IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext
        (IsScalarTower.algebraMap_apply k (abstractFixedField K (SeparableClosure K) H.field)
          (SeparableClosure K) x))
    have _ : FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      FiniteDimensional.right K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field)
    have _ : IsGalois (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.tower_top_of_isGalois K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field)
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) H.field) :=
      (isCurveOver k (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) T.field)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field),
      finiteArtin k K (abstractFixedField K (SeparableClosure K) T.field)
          (IdeleClassGroup.norm (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        Abelianization.map
          (AlgEquiv.restrictScalarsHom
            (S := abstractFixedField K (SeparableClosure K) H.field)
            (A := abstractFixedField K (SeparableClosure K) T.field) K :
            Gal((abstractFixedField K (SeparableClosure K) T.field)/
              (abstractFixedField K (SeparableClosure K) H.field)) →*
            Gal((abstractFixedField K (SeparableClosure K) T.field)/K))
          (finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
            (abstractFixedField K (SeparableClosure K) T.field) c) := by
  intro cE aKE sKE akE aFE sFE mFE hkFA hKFE hKF hKE hKFgal hKEgal hkFE hFE hFEgal
    hFprincipal hEprincipal c
  let r : Gal((abstractFixedField K (SeparableClosure K) T.field)/
      (abstractFixedField K (SeparableClosure K) H.field)) →*
      Gal((abstractFixedField K (SeparableClosure K) T.field)/K) :=
    AlgEquiv.restrictScalarsHom
      (S := abstractFixedField K (SeparableClosure K) H.field)
      (A := abstractFixedField K (SeparableClosure K) T.field) K
  have hLower :
      finiteArtin k K (abstractFixedField K (SeparableClosure K) T.field)
          (IdeleClassGroup.norm (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        Abelianization.map r (fixedFieldArtin k K (SeparableClosure K) H T c) := by
    with_reducible_and_instances
      exact finiteArtin_norm_eq_ambientFixedFieldArtin k K H T c
  have hUpperRestricted :
      Abelianization.map r (fixedFieldArtin k K (SeparableClosure K) H T c) =
        Abelianization.map r
          (finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
            (abstractFixedField K (SeparableClosure K) T.field) c) := by
    have hUpper :
        finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
            (abstractFixedField K (SeparableClosure K) T.field) c =
          fixedFieldArtin k K (SeparableClosure K) H T c := by
      exact finiteArtin_eq_fixedFieldArtin k K H T c
    exact congrArg (Abelianization.map r) hUpper.symm
  with_reducible_and_instances exact Eq.trans hLower hUpperRestricted

end FunctionField
