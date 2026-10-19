/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldNorm
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension

/-!
# Finite abelian reciprocity on actual fixed fields

For an abelian extension the Artin symbol takes values in the actual relative
Galois group. The commutative abstract quotient gives the canonical inverse
to abelianization, and the actual fixed-field comparison transports it.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The Artin homomorphism with values in the actual finite abelian Galois group. -/
def abelianFixedFieldArtin (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    IdeleClassGroup k (abstractFixedField K Ω H.field) →*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) := by
  intro hFfinite aFE
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  let e := eG.abelianizationCongr.symm.trans
    ((Abelianization.equivOfComm (H := L.extensionQuotient)).symm.trans eG)
  exact e.toMonoidHom.comp (fixedFieldArtin k K Ω H L.toFiniteGaloisExtension)

/-- Every relative Galois element is realized by an actual idele class. -/
theorem abelianFixedFieldArtin_surjective (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    Function.Surjective (abelianFixedFieldArtin k K Ω H L) := by
  intro hFfinite aFE
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  let e := eG.abelianizationCongr.symm.trans
    ((Abelianization.equivOfComm (H := L.extensionQuotient)).symm.trans eG)
  exact e.surjective.comp (fixedFieldArtin_surjective k K Ω H L.toFiniteGaloisExtension)

/-- Removing abelianization preserves exactly the trivial Artin values. -/
theorem abelianFixedFieldArtin_eq_one_iff (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      abelianFixedFieldArtin k K Ω H L c = 1 ↔
        fixedFieldArtin k K Ω H L.toFiniteGaloisExtension c = 1 := by
  intro hFfinite aFE c
  let eG : L.extensionQuotient ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  let e := eG.abelianizationCongr.symm.trans
    ((Abelianization.equivOfComm (H := L.extensionQuotient)).symm.trans eG)
  exact e.map_eq_one_iff

end FunctionField
