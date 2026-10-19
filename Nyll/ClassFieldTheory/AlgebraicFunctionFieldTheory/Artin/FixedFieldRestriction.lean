/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.GaloisRestriction
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.RestrictionSymbol

/-!
# Compatibility of finite Artin maps with actual Galois restriction

For two finite Galois fixed fields over the same base, restricting the upper
Artin symbol to the lower field gives the lower Artin symbol. The target map
is the actual restriction of field automorphisms.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Finite Artin symbols commute with actual restriction in a tower of Galois fields. -/
theorem fixedFieldArtin_restrictNormal
    (H : FiniteAbstractField Gal(Ω/K)) (L M : FiniteGaloisSubextension H.field)
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
      Abelianization.map
          (AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H.field)
            (K₁ := abstractFixedField K Ω M.field) (abstractFixedField K Ω L.field))
          (fixedFieldArtin k K Ω H M c) = fixedFieldArtin k K Ω H L c := by
  intro hFfinite aFL aFM aLM hFLM hLgal c
  have hLfinite := L.finite
  have hMfinite := M.finite
  let A := ideleClassRepresentation k K Ω
  let D := fullConstantDegreeData k K Ω
  let v := ideleClassValuationData k K Ω
  have hcf := ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω
  let a := abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c)
  let z := ((D.normResidueSymbol A v hcf H M)
    (finiteNormClass A H.field M.field M.below a)).toMul
  have hg := abstractFixedField_restrictNormal_abelianization K Ω H.field L.field M.field
    L.below M.below hML L.normal M.normal z
  have hr := normResidueSymbol_restriction_finiteNormClass D A v hcf H L M hML a
  change Abelianization.map
      (AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H.field)
        (K₁ := abstractFixedField K Ω M.field) (abstractFixedField K Ω L.field))
      ((abstractExtensionQuotientEquivGaloisGroup K Ω H.field M.field
        M.below M.normal).abelianizationCongr z) =
    (abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field
      L.below L.normal).abelianizationCongr
        (((D.normResidueSymbol A v hcf H L)
          (finiteNormClass A H.field L.field L.below a)).toMul)
  rw [hg]
  exact congrArg
    (abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field
      L.below L.normal).abelianizationCongr hr

end FunctionField
