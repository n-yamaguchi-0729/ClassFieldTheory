/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormalizedValuation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.UnramifiedIntegerSymbol

/-!
# Frobenius normalization for the constant-field degree datum

For an extension unramified with respect to the actual constant-field
degree datum, the Artin symbol is arithmetic Frobenius raised to the
normalized degree of the actual idele class. This concerns the constant
quotient of the class formation; comparison with every local unramified
Artin map is a separate statement.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Reciprocity on a constant-unramified fixed-field extension is its normalized-degree
power of the actual automorphism obtained from arithmetic Frobenius. -/
theorem fixedFieldArtin_unramified_zpow (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field)
    (hu : L.IsUnramified (fullConstantDegreeData k K Ω)) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    let _ := L.finite
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      fixedFieldArtin k K Ω H L c = Abelianization.of
        ((abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
          (L.extensionQuotientMulEquiv.symm
            ((fullConstantDegreeData k K Ω).unramifiedFrobenius
              (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω))
              L.field L.below))) ^
          (IdeleClassGroup.normalizedDegree (k := k)
            (K := abstractFixedField K Ω H.field) c).toAdd) := by
  intro hFfinite aFE hrelfinite c
  let D := fullConstantDegreeData k K Ω
  let A := ideleClassRepresentation k K Ω
  let v := ideleClassValuationData k K Ω
  have hcf := ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω
  let a := abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c)
  let z := (IdeleClassGroup.normalizedDegree (k := k)
    (K := abstractFixedField K Ω H.field) c).toAdd
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  have hv : (v.valuationAt H a : ZHat) = (z : ZHat) :=
    ideleClassValuationData_valuationAt k K Ω H c
  have hs := normResidueSymbol_unramified_integer D A v hcf H L hu a z hv
  change eG.abelianizationCongr
      ((D.normResidueSymbol A v hcf H L)
        (finiteNormClass A H.field L.field L.below a)).toMul =
    Abelianization.of ((eG (L.extensionQuotientMulEquiv.symm
      (D.unramifiedFrobenius (H.toFiniteResidueAbstractField D) L.field L.below))) ^ z)
  rw [hs, abelianizationCongr_of, map_zpow]

end FunctionField
