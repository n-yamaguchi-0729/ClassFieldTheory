/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldConstantSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormalizedDegreeOne

/-!
# Frobenius values after a concrete fixed-field presentation

The arithmetic Frobenius formula survives the degree-one change of the
base field used to define native finite reciprocity.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K L Ω : Type) [Field k] [Finite k] [Field K] [Field L] [Field Ω]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Constant-unramified reciprocity is the normalized-degree power of transported Frobenius. -/
theorem normQuotientEquivOfFixedFieldPresentation_unramified
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (eF : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE : L ≃ₐ[K] abstractFixedField K Ω T.field)
    (hu : T.IsUnramified (fullConstantDegreeData k K Ω)) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : IsGalois K (abstractFixedField K Ω H.field) := IsGalois.of_algEquiv eF
    let aFE : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω T.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    let hKFE : IsScalarTower K (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let hFdegree : Module.finrank K (abstractFixedField K Ω H.field) = 1 := by
      rw [← eF.toLinearEquiv.finrank_eq, Module.finrank_self]
    ∀ c : IdeleClassGroup k K,
      normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE (QuotientGroup.mk c) =
        Abelianization.of
          ((((ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
              (K := K) (F := abstractFixedField K Ω H.field)
              (E := abstractFixedField K Ω T.field) hFdegree).trans
            (AlgEquiv.autCongr eE).symm)
            (abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
              (T.extensionQuotientMulEquiv.symm
                ((fullConstantDegreeData k K Ω).unramifiedFrobenius
                  (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω))
                  T.field T.below)))) ^
              (IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd) := by
  intro hKFfinite hKFgal aFE hKFE hFdegree c
  let eG : Gal((abstractFixedField K Ω T.field)/(abstractFixedField K Ω H.field)) ≃*
      Gal(L/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hFdegree).trans
      (AlgEquiv.autCongr eE).symm
  let φ : Gal((abstractFixedField K Ω T.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
      (T.extensionQuotientMulEquiv.symm
        ((fullConstantDegreeData k K Ω).unramifiedFrobenius
          (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) T.field T.below))
  have hm := normQuotientEquivOfFixedFieldPresentation_mk k K L Ω H T eF eE c
  change normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE (QuotientGroup.mk c) =
    Abelianization.of ((eG φ) ^ (IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd)
  calc
    _ = eG.abelianizationCongr (fixedFieldArtin k K Ω H T
        (IdeleClassGroup.baseChange (k := k) (K := K)
          (L := abstractFixedField K Ω H.field) c)) := hm
    _ = eG.abelianizationCongr (Abelianization.of
        (φ ^ (IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd)) := by
      apply congrArg eG.abelianizationCongr
      rw [fixedFieldArtin_unramified_zpow k K Ω H T hu,
        IdeleClassGroup.normalizedDegree_baseChange_of_finrank_one hFdegree]
      rfl
    _ = _ := by rw [abelianizationCongr_of, map_zpow]

end FunctionField
