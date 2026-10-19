/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldRestriction

/-!
# Restriction of actual finite abelian Artin symbols

The abelian Artin map recovers the abelianized symbol under the canonical
projection. Injectivity of that projection for abelian Galois groups then
proves compatibility with actual field restriction without changing the
native group structure on field automorphisms.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The actual abelian symbol recovers the abelianized finite symbol. -/
theorem abelianFixedFieldArtin_of (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      Abelianization.of (abelianFixedFieldArtin k K Ω H L c) =
        fixedFieldArtin k K Ω H L.toFiniteGaloisExtension c := by
  intro hFfinite aFL c
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  let e := Abelianization.equivOfComm (H := L.extensionQuotient)
  let z : Abelianization
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    fixedFieldArtin k K Ω H L.toFiniteGaloisExtension c
  change Abelianization.of (eG (e.symm (eG.abelianizationCongr.symm z))) = z
  rw [← abelianizationCongr_of]
  change eG.abelianizationCongr (e (e.symm (eG.abelianizationCongr.symm z))) = z
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- Actual finite abelian Artin symbols commute with field restriction. -/
theorem abelianFixedFieldArtin_restrictNormal
    (H : FiniteAbstractField Gal(Ω/K)) (L M : FiniteAbelianSubextension H.field)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω M.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω M.below)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω L.field) (abstractFixedField K Ω M.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hML)).toRingHom.toAlgebra
    let _ : IsScalarTower (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field)
        (abstractFixedField K Ω M.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H.field)
          (K₁ := abstractFixedField K Ω M.field) (abstractFixedField K Ω L.field)
          (abelianFixedFieldArtin k K Ω H M c) = abelianFixedFieldArtin k K Ω H L c := by
  intro hFfinite aFL aFM aLM hFLM hLgal c
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  apply eG.symm.injective
  apply (Abelianization.equivOfComm (H := L.extensionQuotient)).injective
  apply eG.abelianizationCongr.injective
  change Abelianization.of
      (eG (eG.symm ((AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H.field)
        (K₁ := abstractFixedField K Ω M.field) (abstractFixedField K Ω L.field))
          (abelianFixedFieldArtin k K Ω H M c)))) =
    Abelianization.of (eG (eG.symm (abelianFixedFieldArtin k K Ω H L c)))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    ← Abelianization.map_of, abelianFixedFieldArtin_of, abelianFixedFieldArtin_of]
  exact fixedFieldArtin_restrictNormal k K Ω H
    L.toFiniteGaloisExtension M.toFiniteGaloisExtension hML c

end FunctionField
