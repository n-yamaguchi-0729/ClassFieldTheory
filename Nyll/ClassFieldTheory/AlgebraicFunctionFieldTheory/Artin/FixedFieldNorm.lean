/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormComparison

/-!
# The actual norm kernel of finite function-field reciprocity

The concrete comparison of abstract and idele-class norms identifies the
kernel of the Artin symbol with the actual all-place norm image.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The finite Artin symbol vanishes exactly on actual idele-class norms. -/
theorem fixedFieldArtin_eq_one_iff_mem_norm (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractRelativeFixedField K Ω L.below) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω L.below) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    have _ : IsScalarTower k K (abstractRelativeFixedField K Ω L.below) :=
      IsScalarTower.of_algebraMap_eq
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
    have _ : AlgebraicCurve.HasPrincipalDivisors k (abstractRelativeFixedField K Ω L.below) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k K (abstractRelativeFixedField K Ω L.below)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      fixedFieldArtin k K Ω H L c = 1 ↔
        c ∈ (IdeleClassGroup.norm (k := k)
          (K := abstractFixedField K Ω H.field) (L := abstractRelativeFixedField K Ω
            L.below)).range := by
  intro hkFΩ hrelfinite hupper hFfinite hEfinite hKFE hkFE hFEfinite hFEgal hkKE hEprincipal c
  let J : FiniteAbstractField Gal(Ω/K) := ⟨L.field, hupper⟩
  rw [fixedFieldArtin_eq_one_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := (abstractFixedClassEquiv k K Ω L.field hupper).surjective b
    have hn := abstractFixedClassEquiv_norm k K Ω H J L.below L.normal a
    have he := (abstractFixedClassEquiv k K Ω H.field H.finite).injective (hn.trans hb)
    exact ⟨a.toMul, congrArg Additive.toMul he⟩
  · rintro ⟨a, ha⟩
    refine ⟨abstractFixedClassEquiv k K Ω L.field hupper (Additive.ofMul a), ?_⟩
    have hn := abstractFixedClassEquiv_norm k K Ω H J L.below L.normal (Additive.ofMul a)
    exact hn.symm.trans
      (congrArg (fun x => abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul x)) ha)

/-- The kernel is the actual all-place idele-class norm subgroup. -/
theorem fixedFieldArtin_ker (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractRelativeFixedField K Ω L.below) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω L.below) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    have _ : IsScalarTower k K (abstractRelativeFixedField K Ω L.below) :=
      IsScalarTower.of_algebraMap_eq
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
    have _ : AlgebraicCurve.HasPrincipalDivisors k (abstractRelativeFixedField K Ω L.below) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k K (abstractRelativeFixedField K Ω L.below)).toHasPrincipalDivisors
    (fixedFieldArtin k K Ω H L).ker =
      (IdeleClassGroup.norm (k := k)
        (K := abstractFixedField K Ω H.field) (L := abstractRelativeFixedField K Ω
          L.below)).range := by
  intro hkFΩ hrelfinite hupper hFfinite hEfinite hKFE hkFE hFEfinite hFEgal hkKE hEprincipal
  apply Subgroup.ext
  intro c
  exact fixedFieldArtin_eq_one_iff_mem_norm k K Ω H L c

/-- Actual norm classes are the actual relative abelianized Galois group. -/
def fixedFieldNormQuotientEquiv (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractRelativeFixedField K Ω L.below) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω L.below) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    have _ : IsScalarTower k K (abstractRelativeFixedField K Ω L.below) :=
      IsScalarTower.of_algebraMap_eq
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
    have _ : AlgebraicCurve.HasPrincipalDivisors k (abstractRelativeFixedField K Ω L.below) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k K (abstractRelativeFixedField K Ω L.below)).toHasPrincipalDivisors
    (IdeleClassGroup k (abstractFixedField K Ω H.field) ⧸
      (IdeleClassGroup.norm (k := k)
        (K := abstractFixedField K Ω H.field) (L := abstractRelativeFixedField K Ω
          L.below)).range) ≃*
      Abelianization Gal((abstractRelativeFixedField K Ω L.below)/(abstractFixedField K Ω
        H.field)) := by
  intro hkFΩ hrelfinite hupper hFfinite hEfinite hKFE hkFE hFEfinite hFEgal hkKE hEprincipal
  exact (QuotientGroup.quotientMulEquivOfEq (fixedFieldArtin_ker k K Ω H L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (fixedFieldArtin k K Ω H L)
      (fixedFieldArtin_surjective k K Ω H L))

/-- On representatives, the norm-quotient isomorphism is the finite Artin symbol. -/
theorem fixedFieldNormQuotientEquiv_mk (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractRelativeFixedField K Ω L.below) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω
      L.below) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractRelativeFixedField K Ω L.below) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    have _ : IsScalarTower k K (abstractRelativeFixedField K Ω L.below) :=
      IsScalarTower.of_algebraMap_eq
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
    have _ : AlgebraicCurve.HasPrincipalDivisors k (abstractRelativeFixedField K Ω L.below) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k K (abstractRelativeFixedField K Ω L.below)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      fixedFieldNormQuotientEquiv k K Ω H L (QuotientGroup.mk c) = fixedFieldArtin k K Ω H L c := by
  intro hkFΩ hrelfinite hupper hFfinite hEfinite hKFE hkFE hFEfinite hFEgal hkKE hEprincipal c
  change QuotientGroup.kerLift (fixedFieldArtin k K Ω H L)
    (QuotientGroup.quotientMulEquivOfEq (fixedFieldArtin_ker k K Ω H L).symm
      (QuotientGroup.mk c)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]

end FunctionField
