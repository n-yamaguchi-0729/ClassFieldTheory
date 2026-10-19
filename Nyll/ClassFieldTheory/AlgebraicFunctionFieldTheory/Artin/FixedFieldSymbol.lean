/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Main
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Valuation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main

/-!
# The finite Artin symbol on actual fixed-field idele classes

The proved function-field class formation defines the norm-residue symbol
on actual idele classes. The actual Galois quotient comparison puts its values
in the abelianization of the relative fixed-field Galois group.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Finite function-field reciprocity on actual idele classes and actual relative Galois groups. -/
def fixedFieldArtin (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    IdeleClassGroup k (abstractFixedField K Ω H.field) →*
      Abelianization Gal((abstractRelativeFixedField K Ω L.below)/
        (abstractFixedField K Ω H.field)) := by
  intro hFfinite
  have hrelfinite := L.finite
  let D := fullConstantDegreeData k K Ω
  let A := ideleClassRepresentation k K Ω
  let v := ideleClassValuationData k K Ω
  let s := D.normResidueSymbol A v (ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω) H L
  let f : Additive (IdeleClassGroup k (abstractFixedField K Ω H.field)) →+
      Additive (Abelianization L.extensionQuotient) :=
    s.toAddMonoidHom.comp ((finiteNormClassHom A H.field L.field L.below).comp
      (abstractFixedClassEquiv k K Ω H.field H.finite).toAddMonoidHom)
  let eG : L.extensionQuotient ≃*
      Gal((abstractRelativeFixedField K Ω L.below)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  exact eG.abelianizationCongr.toMonoidHom.comp
    ((MulEquiv.multiplicativeAdditive (Abelianization L.extensionQuotient)).toMonoidHom.comp
      (AddMonoidHom.toMultiplicativeRight f))

/-- Every element of the actual relative abelianized Galois group is an Artin value. -/
theorem fixedFieldArtin_surjective (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    Function.Surjective (fixedFieldArtin k K Ω H L) := by
  intro hFfinite
  have hrelfinite := L.finite
  let s := (fullConstantDegreeData k K Ω).normResidueSymbol (ideleClassRepresentation k K Ω)
    (ideleClassValuationData k K Ω) (ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω) H L
  let eG : L.extensionQuotient ≃*
      Gal((abstractRelativeFixedField K Ω L.below)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  intro σ
  obtain ⟨τ, rfl⟩ := eG.abelianizationCongr.surjective σ
  obtain ⟨q, hq⟩ := s.surjective (Additive.ofMul τ)
  obtain ⟨a, ha⟩ := finiteNormClass_surjective (ideleClassRepresentation k K Ω)
    H.field L.field L.below q
  obtain ⟨c, hc⟩ := (abstractFixedClassEquiv k K Ω H.field H.finite).surjective a
  refine ⟨c.toMul, ?_⟩
  change eG.abelianizationCongr
    (s (finiteNormClass (ideleClassRepresentation k K Ω) H.field L.field L.below
      (abstractFixedClassEquiv k K Ω H.field H.finite c))).toMul = eG.abelianizationCongr τ
  rw [hc, ha, hq]
  rfl

/-- Triviality of the symbol is exactly membership in the proved abstract norm image. -/
theorem fixedFieldArtin_eq_one_iff (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteGaloisSubextension H.field) :
    have _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ := L.finite
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      fixedFieldArtin k K Ω H L c = 1 ↔
        abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c) ∈
          finiteNormSubgroup (ideleClassRepresentation k K Ω) H.field L.field L.below := by
  intro hFfinite hrelfinite c
  let s := (fullConstantDegreeData k K Ω).normResidueSymbol (ideleClassRepresentation k K Ω)
    (ideleClassValuationData k K Ω) (ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω) H L
  let eG : L.extensionQuotient ≃*
      Gal((abstractRelativeFixedField K Ω L.below)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  change eG.abelianizationCongr
    (s (finiteNormClass (ideleClassRepresentation k K Ω) H.field L.field L.below
      (abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c)))).toMul = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  change s (finiteNormClass (ideleClassRepresentation k K Ω) H.field L.field L.below
    (abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c))) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  exact finiteNormClass_eq_zero_iff _ _ _ _ _

end FunctionField
