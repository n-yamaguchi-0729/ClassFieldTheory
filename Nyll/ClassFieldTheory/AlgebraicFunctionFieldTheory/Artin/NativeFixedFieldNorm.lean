/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativePresentation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NormCompatibility

/-!
# Native norm reciprocity on actual finite fixed fields

The native symbol at the original base is evaluated on an actual norm through
its degree-one intrinsic presentation. The proved ambient norm formula then
identifies this value with scalar restriction of the upper ambient symbol.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

/-- A finite normal abstract field is a finite Galois extension of the intrinsic base. -/
private def intrinsicGaloisSubextensionOfFiniteField
    (K : Type) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal] :
    FiniteGaloisSubextension (intrinsicFiniteAbstractBase K).field := by
  have hB : (intrinsicFiniteAbstractBase K).field = baseField Gal(SeparableClosure K/K) :=
    congrArg FiniteAbstractField.field (intrinsicFiniteAbstractBase_eq_base K)
  have hHB : H.field.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup := by
    rw [hB]
    exact le_baseField H.field
  exact ⟨H.field, hHB, inferInstance,
    (congrArg (fun V : ClosedSubgroup Gal(SeparableClosure K/K) =>
      Finite (V.toSubgroup ⧸ H.field.toSubgroup.subgroupOf V.toSubgroup)) hB).mpr H.finite⟩

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

/-- The lower native symbol agrees with restriction of the upper ambient symbol.
Only the actual finite-field and principal-divisor structures are used here. -/
theorem finiteArtin_norm_eq_ambientFixedFieldArtin
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field)
    [H.field.toSubgroup.Normal] [T.field.toSubgroup.Normal]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H.field)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) T.field)]
    [AlgebraicCurve.HasPrincipalDivisors k
      (abstractFixedField K (SeparableClosure K) H.field)]
    [AlgebraicCurve.HasPrincipalDivisors k
      (abstractFixedField K (SeparableClosure K) T.field)]
    (c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field)) :
    let _ : CommSemiring (abstractFixedField K (SeparableClosure K) T.field) :=
      (inferInstance : Field (abstractFixedField K (SeparableClosure K) T.field)).toSemifield
        |>.toCommSemiring
    let aKE : Algebra K (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := K)
        (abstractFixedField K (SeparableClosure K) T.field)
    let _ : SMul K (abstractFixedField K (SeparableClosure K) T.field) := aKE.toSMul
    let aFE : Algebra (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (abstractRelativeFixedField K (SeparableClosure K) T.below).algebra
    let _ : SMul (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toSMul
    have _ : IsScalarTower K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
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
        (fixedFieldArtin k K (SeparableClosure K) H T c) := by
  intro cE aKE sKE aFE sFE hKFE
  let HB := intrinsicGaloisSubextensionOfFiniteField K H
  have hTnormal : T.toFiniteAbstractFieldExtension.field.field.toSubgroup.Normal := by
    change T.field.toSubgroup.Normal
    infer_instance
  let UB := intrinsicGaloisSubextensionOfFiniteField K T.toFiniteAbstractFieldExtension.field
  have hHB : H.field.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup := HB.below
  have hUB : T.field.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup := UB.below
  have hHfinite : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      extensionSubgroup (intrinsicFiniteAbstractBase K).field H.field hHB) := HB.finite
  have hUfinite : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      extensionSubgroup (intrinsicFiniteAbstractBase K).field T.field hUB) := UB.finite
  have hHnormal : (extensionSubgroup (intrinsicFiniteAbstractBase K).field
      H.field hHB).Normal := HB.normal
  have hUnormal : (extensionSubgroup (intrinsicFiniteAbstractBase K).field
      T.field hUB).Normal := UB.normal
  have _ : Finite (H.field.toSubgroup ⧸
      extensionSubgroup H.field T.field T.below) := T.finite
  have _ : (extensionSubgroup H.field T.field T.below).Normal := T.normal
  have hambient := fixedFieldArtin_norm_of_basePresentation k K (SeparableClosure K)
    (intrinsicFiniteAbstractBase K) H hHB
    T.field hUB T.below hHnormal
    (finiteGaloisBaseFixedFieldEquiv K) c
  extract_lets n at hambient
  have hnorm : n = IdeleClassGroup.norm (k := k) (K := K)
      (L := abstractFixedField K (SeparableClosure K) H.field) c := by
    rfl
  have hnative := finiteArtin_eq_intrinsicFixedField_restrict k K T.field hUB n
  have hvalue :
      finiteArtin k K (abstractFixedField K (SeparableClosure K) T.field) n =
        Abelianization.map
          (AlgEquiv.restrictScalarsHom
            (S := abstractFixedField K (SeparableClosure K) H.field)
            (A := abstractFixedField K (SeparableClosure K) T.field) K :
            Gal((abstractFixedField K (SeparableClosure K) T.field)/
              (abstractFixedField K (SeparableClosure K) H.field)) →*
            Gal((abstractFixedField K (SeparableClosure K) T.field)/K))
          (fixedFieldArtin k K (SeparableClosure K) H T c) := by
    with_reducible_and_instances exact Eq.trans hnative hambient
  exact (congrArg (finiteArtin k K
    (abstractFixedField K (SeparableClosure K) T.field)) hnorm.symm).trans hvalue


end FunctionField
