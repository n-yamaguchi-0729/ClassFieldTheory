/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FixedFieldFiniteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FixedFieldAbsoluteGalois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Native absolute reciprocity in the original fixed subgroup

The original ambient subgroup acts on each actual relative fixed field.
Its finite restriction maps descend to the topological abelianization for
abelian relative extensions. Conjugation by an actual separable-closure
equivalence carries native absolute reciprocity to this subgroup, and every
finite projection is the original native Artin automorphism.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory ProCGroups.Abelian
open scoped IsMulCommutative

section Artin

variable (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsGalois K Ω]
    [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]

/-- Native absolute reciprocity, expressed in the actual original ambient
subgroup by an actual equivalence of separable closures. -/
def fixedFieldAbsoluteArtinOfClosure
    (H : FiniteAbstractField Gal(Ω/K))
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω) :
    have _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K Ω H.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K Ω H.field)).toHasPrincipalDivisors
    IdeleClassGroup k (abstractFixedField K Ω H.field) →ₜ*
      TopologicalAbelianization H.field.toSubgroup := by
  intro hfinite hprincipal
  exact (ContinuousMonoidHom.toContinuousMonoidHom
    (fixedFieldAbsoluteAbelianEquivOfClosure K Ω H e)).comp
      (absoluteArtin k (abstractFixedField K Ω H.field))

/-- Every original subgroup coordinate of transported native absolute
reciprocity is the original finite native Artin automorphism. -/
theorem fixedFieldAbsoluteArtinOfClosure_projection
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    [IsMulCommutative T.extensionQuotient]
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω) :
    have _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    have _ : FiniteDimensional (abstractFixedField K Ω H.field)
        (abstractRelativeFixedField K Ω T.below) :=
      abstractRelativeFixedField_finiteDimensional K Ω H.field T.field
        T.below H.finite T.finite
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    have _ : IsScalarTower (RatFunc k) (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ (RatFunc k) K (abstractFixedField K Ω H.field) Ω
    have _ : IsAbelianGalois (abstractFixedField K Ω H.field)
        (abstractRelativeFixedField K Ω T.below) :=
      fixedFieldRelative_isAbelianGalois K Ω H T
    have _ : AlgebraicCurve.HasPrincipalDivisors k (abstractFixedField K Ω H.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K Ω H.field)).toHasPrincipalDivisors
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractRelativeFixedField K Ω T.below) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k
        (abstractFixedField K Ω H.field)
        (abstractRelativeFixedField K Ω T.below)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      fixedFieldFiniteArtinProjection K Ω H T
          (fixedFieldAbsoluteArtinOfClosure k K Ω H e c) =
        abelianFiniteArtin k (abstractFixedField K Ω H.field)
          (abstractRelativeFixedField K Ω T.below) c := by
  intro hKF hFE hkFΩ hRFΩ hab hFprincipal hEprincipal c
  change fixedFieldFiniteArtinProjection K Ω H T
      (fixedFieldAbsoluteAbelianEquivOfClosure K Ω H e
        (absoluteArtin k (abstractFixedField K Ω H.field) c)) = _
  rw [fixedFieldFiniteArtinProjection_closure K Ω H T e]
  exact absoluteArtin_restrictionOfEmbedding k (abstractFixedField K Ω H.field)
    (abstractRelativeFixedField K Ω T.below)
    (e.symm.toAlgHom.comp (abstractRelativeFixedField K Ω T.below).val) c

end Artin

end FunctionField
