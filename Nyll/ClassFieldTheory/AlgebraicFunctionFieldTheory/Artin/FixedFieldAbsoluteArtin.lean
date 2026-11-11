/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

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

section Restrictions

variable (K : Type v) (Ω : Type w) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)

/-- Restrict the actual ambient subgroup to the relative finite fixed field. -/
def fixedFieldSubgroupFiniteRestriction :
    H.field.toSubgroup →ₜ*
      Gal((abstractRelativeFixedField K Ω T.below)/(abstractFixedField K Ω H.field)) := by
  let F := abstractFixedField K Ω H.field
  let E := abstractRelativeFixedField K Ω T.below
  have hgalΩ : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  have hfinite : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field T.field
      T.below H.finite T.finite
  have hgal : IsGalois F E :=
    abstractRelativeFixedField_isGalois K Ω H.field T.field T.below T.normal
  exact
    { toMonoidHom := (AlgEquiv.restrictNormalHom E).comp
        (finiteAbstractSubgroupGaloisEquiv K Ω H).toMonoidHom
      continuous_toFun := (InfiniteGalois.restrictNormalHom_continuous E).comp
        (finiteAbstractSubgroupGaloisEquiv K Ω H).continuous_toFun }

/-- The finite restriction is characterized by the original ambient action. -/
theorem fixedFieldSubgroupFiniteRestriction_commutes
    (σ : H.field.toSubgroup) (x : abstractRelativeFixedField K Ω T.below) :
    algebraMap (abstractRelativeFixedField K Ω T.below) Ω
        (fixedFieldSubgroupFiniteRestriction K Ω H T σ x) =
      σ.val (algebraMap (abstractRelativeFixedField K Ω T.below) Ω x) := by
  have hgal : IsGalois (abstractFixedField K Ω H.field)
      (abstractRelativeFixedField K Ω T.below) :=
    abstractRelativeFixedField_isGalois K Ω H.field T.field T.below T.normal
  exact AlgEquiv.restrictNormal_commutes
    (finiteAbstractSubgroupGaloisEquiv K Ω H σ)
    (abstractRelativeFixedField K Ω T.below) x

/-- Commutativity of the original relative quotient gives the actual
abelian Galois structure on its relative fixed field. -/
theorem fixedFieldRelative_isAbelianGalois [IsMulCommutative T.extensionQuotient] :
    IsAbelianGalois (abstractFixedField K Ω H.field)
      (abstractRelativeFixedField K Ω T.below) := by
  have hgal : IsGalois (abstractFixedField K Ω H.field)
      (abstractRelativeFixedField K Ω T.below) :=
    abstractRelativeFixedField_isGalois K Ω H.field T.field T.below T.normal
  let e := T.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal)
  refine { is_comm.comm := ?_ }
  intro σ τ
  apply e.symm.injective
  rw [map_mul, map_mul, mul_comm]

variable [IsMulCommutative T.extensionQuotient]

/-- The actual finite restriction on the original subgroup abelianization. -/
def fixedFieldFiniteArtinProjection :
    TopologicalAbelianization H.field.toSubgroup →ₜ*
      Gal((abstractRelativeFixedField K Ω T.below)/(abstractFixedField K Ω H.field)) := by
  have hfinite : FiniteDimensional (abstractFixedField K Ω H.field)
      (abstractRelativeFixedField K Ω T.below) :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field T.field
      T.below H.finite T.finite
  have hab : IsAbelianGalois (abstractFixedField K Ω H.field)
      (abstractRelativeFixedField K Ω T.below) :=
    fixedFieldRelative_isAbelianGalois K Ω H T
  exact TopologicalAbelianization.lift (fixedFieldSubgroupFiniteRestriction K Ω H T)

/-- On representatives, the projection is literal field restriction. -/
theorem fixedFieldFiniteArtinProjection_mk (σ : H.field.toSubgroup) :
    fixedFieldFiniteArtinProjection K Ω H T
        (TopologicalAbelianization.mk H.field.toSubgroup σ) =
      fixedFieldSubgroupFiniteRestriction K Ω H T σ := rfl

/-- Actual closure conjugation and original subgroup restriction have the
same finite coordinate, through the explicit embedded relative field. -/
theorem fixedFieldFiniteArtinProjection_closure
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω) :
    have _ : FiniteDimensional (abstractFixedField K Ω H.field)
        (abstractRelativeFixedField K Ω T.below) :=
      abstractRelativeFixedField_finiteDimensional K Ω H.field T.field
        T.below H.finite T.finite
    have _ : IsAbelianGalois (abstractFixedField K Ω H.field)
        (abstractRelativeFixedField K Ω T.below) :=
      fixedFieldRelative_isAbelianGalois K Ω H T
    ∀ z : localAbsoluteAbelianProfinite (abstractFixedField K Ω H.field),
      fixedFieldFiniteArtinProjection K Ω H T
          (fixedFieldAbsoluteAbelianEquivOfClosure K Ω H e z) =
        absoluteRestrictionOfEmbedding (abstractFixedField K Ω H.field)
          (abstractRelativeFixedField K Ω T.below)
          (e.symm.toAlgHom.comp (abstractRelativeFixedField K Ω T.below).val) z := by
  intro hfinite hab z
  refine QuotientGroup.induction_on z ?_
  intro σ
  let E := abstractRelativeFixedField K Ω T.below
  let i := e.symm.toAlgHom.comp E.val
  change fixedFieldSubgroupFiniteRestriction K Ω H T
      (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e σ) =
    embeddedFiniteRestriction (abstractFixedField K Ω H.field) E i σ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  calc
    algebraMap E Ω (fixedFieldSubgroupFiniteRestriction K Ω H T
        (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e σ) x) =
        (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e σ).val (algebraMap E Ω x) :=
      fixedFieldSubgroupFiniteRestriction_commutes K Ω H T _ x
    _ = e (σ (i x)) := rfl
    _ = e (i (embeddedFiniteRestriction (abstractFixedField K Ω H.field) E i σ x)) :=
      congrArg e (embeddedFiniteRestriction_commutes
        (abstractFixedField K Ω H.field) E i σ x).symm
    _ = algebraMap E Ω (embeddedFiniteRestriction
        (abstractFixedField K Ω H.field) E i σ x) := e.apply_symm_apply _

end Restrictions

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
