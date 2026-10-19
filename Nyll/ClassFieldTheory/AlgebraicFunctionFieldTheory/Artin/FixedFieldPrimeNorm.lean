/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Main
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormalizedValuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormComparison

/-!
# Actual prime-norm representatives for finite function-field reciprocity

For an abelian target, the auxiliary fixed field of a positive Frobenius
lift is Galois over the base. The quotient above the target inertia embeds
in the product of the abelian target quotient and the degree quotient,
which proves this normality without an additional hypothesis.

A normalized-degree-one idele class of that actual auxiliary field then
has a norm whose Artin value is the prescribed Frobenius restriction. This
provides actual representatives for comparing reciprocity constructions.
-/

noncomputable section

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open scoped IsMulCommutative

namespace ClassFormation.DegreeData

private theorem extensionInertiaWithin_quotient_isMulCommutative
    {G : Type*} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (H : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLH : L.toSubgroup ≤ H.field.toSubgroup)
    [(extensionSubgroup H.field L hLH).Normal]
    [IsMulCommutative (H.field.toSubgroup ⧸ extensionSubgroup H.field L hLH)] :
    IsMulCommutative (H.field.toSubgroup ⧸ D.extensionInertiaWithin H.field L hLH) := by
  apply IsMulCommutative.of_comm
  intro a b
  refine QuotientGroup.induction_on a ?_
  intro x
  refine QuotientGroup.induction_on b ?_
  intro y
  change (QuotientGroup.mk (x * y) :
    H.field.toSubgroup ⧸ D.extensionInertiaWithin H.field L hLH) =
      QuotientGroup.mk (y * x)
  apply QuotientGroup.eq.mpr
  constructor
  · apply QuotientGroup.eq.mp
    exact mul_comm
      (QuotientGroup.mk x : H.field.toSubgroup ⧸ extensionSubgroup H.field L hLH)
      (QuotientGroup.mk y)
  · rw [← D.normalizedDegree_ker H]
    change D.normalizedDegree H ((x * y)⁻¹ * (y * x)) = 1
    rw [map_mul, map_inv, map_mul, map_mul,
      mul_comm (D.normalizedDegree H y) (D.normalizedDegree H x), inv_mul_cancel]

/-- An abelian finite target makes its Frobenius auxiliary fixed field
Galois over the base. -/
theorem frobeniusFixedField_normal_of_abelian
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : DegreeData G) (H : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLH : L.toSubgroup ≤ H.field.toSubgroup)
    [(extensionSubgroup H.field L hLH).Normal]
    [IsMulCommutative (H.field.toSubgroup ⧸ extensionSubgroup H.field L hLH)]
    (σ : D.FrobeniusElements H L hLH) :
    (extensionSubgroup H.field (D.frobeniusFixedField H L hLH σ)
      (D.frobeniusFixedField_le H L hLH σ)).Normal := by
  have hcomm : IsMulCommutative
      (H.field.toSubgroup ⧸ D.extensionInertiaWithin H.field L hLH) :=
    extensionInertiaWithin_quotient_isMulCommutative D H L hLH
  rw [D.extensionSubgroup_frobeniusFixedField H L hLH σ]
  change ((D.frobeniusClosure H L hLH σ).toSubgroup.comap
    (QuotientGroup.mk' (D.extensionInertiaWithin H.field L hLH))).Normal
  infer_instance

end ClassFormation.DegreeData

namespace FunctionField

attribute [local instance]
  ambientFrobeniusAuxiliaryAlgebra
  ambientFrobeniusAuxiliaryConstantAlgebra

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The norm of a normalized-degree-one class in the actual Frobenius
auxiliary field has the specified finite Artin value. All field, norm and
valuation comparisons are supplied by the concrete function-field construction. -/
theorem fixedFieldArtin_frobenius_primeNorm
    (H : FiniteAbstractField Gal(Ω/K)) (L : FiniteGaloisSubextension H.field)
    [IsMulCommutative L.extensionQuotient]
    (σ : (fullConstantDegreeData k K Ω).FrobeniusElements
      (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) L.field L.below) :
    have _ : IsScalarTower k (abstractFixedField K Ω H.field) Ω :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K Ω H.field) Ω
    let D := fullConstantDegreeData k K Ω
    let _ : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field L.field L.below) :=
      L.finite
    let hLcomm : IsMulCommutative
        (H.field.toSubgroup ⧸ extensionSubgroup H.field L.field L.below) := by
      change IsMulCommutative L.extensionQuotient
      infer_instance
    let HR := H.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField HR L.field L.below σ
    let hSH : S.toSubgroup ≤ H.field.toSubgroup :=
      D.frobeniusFixedField_le HR L.field L.below σ
    let hSfinite := D.frobeniusFixedField_absoluteFinite H L.field L.below σ
    let hSnormal : (extensionSubgroup H.field S hSH).Normal := by
      have hcomm : IsMulCommutative
          (HR.field.toSubgroup ⧸ extensionSubgroup HR.field L.field L.below) := by
        change IsMulCommutative
          (H.field.toSubgroup ⧸ extensionSubgroup H.field L.field L.below)
        exact hLcomm
      exact D.frobeniusFixedField_normal_of_abelian HR L.field L.below σ
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      abstractFixedField_finiteDimensional K Ω S hSfinite
    let _ : IsScalarTower K (abstractFixedField K Ω H.field)
        (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field)
        (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field)
        (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field)
        (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      abstractRelativeFixedField_isGalois K Ω H.field S hSH hSnormal
    have _ : IsScalarTower k K (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      IsScalarTower.of_algebraMap_eq
        (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
    have _ : AlgebraicCurve.HasPrincipalDivisors k (ambientFrobeniusAuxiliaryField k K Ω H L σ) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k K (ambientFrobeniusAuxiliaryField k K Ω H L σ)).toHasPrincipalDivisors
    let eG : L.extensionQuotient ≃*
        Gal((abstractRelativeFixedField K Ω L.below)/(abstractFixedField K Ω H.field)) :=
      abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
    ∀ c : IdeleClassGroup k (ambientFrobeniusAuxiliaryField k K Ω H L σ),
      (IdeleClassGroup.normalizedDegree (k := k) (K := ambientFrobeniusAuxiliaryField k K Ω H L σ)
        c).toAdd = 1 →
      fixedFieldArtin k K Ω H L
        (IdeleClassGroup.norm (k := k) (K := abstractFixedField K Ω H.field)
          (L := ambientFrobeniusAuxiliaryField k K Ω H L σ) c) =
        Abelianization.of (eG (D.frobeniusRestriction HR L.field L.below σ)) := by
  intro hkFΩ D hLrelative hLcomm HR S hSH hSfinite hSnormal hHfinite hSdimension
    hKHS hkHS hHSfinite hHSgalois hkKS hSprincipal eG c hc
  have : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field S hSH) :=
    D.frobeniusFixedField_finite HR L.field L.below σ
  let A := ideleClassRepresentation k K Ω
  let v := ideleClassValuationData k K Ω
  have hcf := ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω
  let SF : FiniteAbstractField Gal(Ω/K) := ⟨S, hSfinite⟩
  let π : ambientFixedAddSubgroup A S :=
    abstractFixedClassEquiv k K Ω S hSfinite (Additive.ofMul c)
  have hπ : v.IsPrimeElement SF π := by
    apply Subtype.ext
    change (v.valuationAt SF π : ZHat) = 1
    have hvaluation := ideleClassValuationData_valuationAt k K Ω SF c
    exact hvaluation.trans
      ((congrArg (fun n : ℤ => (n : ZHat)) hc).trans Int.cast_one)
  let q : L.extensionQuotient := D.frobeniusRestriction HR L.field L.below σ
  have hprime := D.finiteReciprocityHom_apply_eq_primeNormClass
    A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
    H L.field L.below (Additive.ofMul q) σ rfl π hπ
  have hnorm := abstractFixedClassEquiv_norm k K Ω H SF hSH hSnormal (Additive.ofMul c)
  have hs := D.normResidueSymbol_finiteReciprocityHom A v hcf H L q
  rw [hprime, ← hnorm] at hs
  change eG.abelianizationCongr
      ((D.normResidueSymbol A v hcf H L)
        (finiteNormClass A H.field L.field L.below
          (abstractFixedClassEquiv k K Ω H.field H.finite
            (Additive.ofMul (IdeleClassGroup.norm (k := k)
              (K := abstractFixedField K Ω H.field)
              (L := ambientFrobeniusAuxiliaryField k K Ω H L σ)
                c))))).toMul =
    Abelianization.of (eG q)
  exact (congrArg eG.abelianizationCongr (congrArg Additive.toMul hs)).trans
    (abelianizationCongr_of eG q)

end FunctionField
