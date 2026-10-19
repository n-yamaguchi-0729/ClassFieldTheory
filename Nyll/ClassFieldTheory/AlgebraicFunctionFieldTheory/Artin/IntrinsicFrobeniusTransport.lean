/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FixedFieldDegreeComparison
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldSpecialization
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusClosure
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusQuotientTransport
import Nyll.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration
import Nyll.ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv

/-!
# Transport of function-field Frobenius quotients across separable closures

The existing algebraic equivalence of absolute Galois subgroups, together
with the concrete comparison of full-constant degrees, identifies extension
inertia and its quotient. No reciprocity comparison is assumed.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra k (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]

-- Shared canonical structures for the actual auxiliary fields. These instances
-- remain local; consumers reuse these exact values when comparing norm maps.
local instance fixedBaseCommSemiring :
    CommSemiring (abstractFixedField K (SeparableClosure K) H.field) :=
  (inferInstance : Field
    (abstractFixedField K (SeparableClosure K) H.field)).toSemifield.toCommSemiring

local instance fixedBaseClosureAlgebra :
    Algebra (abstractFixedField K (SeparableClosure K) H.field) (SeparableClosure
      (abstractFixedField K (SeparableClosure K) H.field)) :=
  IntermediateField.algebra'
    (R' := abstractFixedField K (SeparableClosure K) H.field)
    (separableClosure (abstractFixedField K (SeparableClosure K) H.field)
      (AlgebraicClosure (abstractFixedField K (SeparableClosure K) H.field)))

local instance fixedBaseClosureSMul :
    SMul (abstractFixedField K (SeparableClosure K) H.field) (SeparableClosure
      (abstractFixedField K (SeparableClosure K) H.field)) :=
  (fixedBaseClosureAlgebra (K := K) (H := H)).toSMul

local instance fixedBaseClosureModule :
    Module (abstractFixedField K (SeparableClosure K) H.field) (SeparableClosure
      (abstractFixedField K (SeparableClosure K) H.field)) :=
  (fixedBaseClosureAlgebra (K := K) (H := H)).toModule

local instance relativeFixedFieldCommSemiring (T : FiniteGaloisSubextension H.field) :
    CommSemiring (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  (inferInstance : Field
    (abstractRelativeFixedField K (SeparableClosure K) T.below)).toSemifield.toCommSemiring

local instance relativeFixedFieldAlgebra (T : FiniteGaloisSubextension H.field) :
    Algebra (abstractFixedField K (SeparableClosure K) H.field) (abstractRelativeFixedField K
      (SeparableClosure K) T.below) :=
  (abstractRelativeFixedField K (SeparableClosure K) T.below).algebra

local instance relativeFixedFieldSMul (T : FiniteGaloisSubextension H.field) :
    SMul (abstractFixedField K (SeparableClosure K) H.field) (abstractRelativeFixedField K
      (SeparableClosure K) T.below) :=
  (relativeFixedFieldAlgebra (K := K) (H := H) T).toSMul

local instance relativeFixedFieldModule (T : FiniteGaloisSubextension H.field) :
    Module (abstractFixedField K (SeparableClosure K) H.field) (abstractRelativeFixedField K
      (SeparableClosure K) T.below) :=
  (relativeFixedFieldAlgebra (K := K) (H := H) T).toModule

local instance fixedBaseAmbientTower :
    IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field) (SeparableClosure K) :=
  IsScalarTower.to₁₃₄ k K (abstractFixedField K (SeparableClosure K) H.field)
    (SeparableClosure K)

local instance relativeFixedFieldFiniteDimensional (T : FiniteGaloisSubextension H.field) :
    FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  abstractRelativeFixedField_finiteDimensional
    K (SeparableClosure K) H.field T.field T.below H.finite T.finite

local instance relativeFixedFieldGalois (T : FiniteGaloisSubextension H.field) :
    IsGalois (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
  abstractRelativeFixedField_isGalois
    K (SeparableClosure K) H.field T.field T.below T.normal

private theorem intrinsicNormalizedDegree_eq_ambientFixedField :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
      (fullConstantDegreeData k F (SeparableClosure F)).normalizedDegree
          ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (fullConstantDegreeData k F (SeparableClosure F))) τ =
        (fullConstantDegreeData k K (SeparableClosure K)).normalizedDegree
          (H.toFiniteResidueAbstractField (fullConstantDegreeData k K (SeparableClosure K)))
          (intrinsicBaseEquivAmbientFixedField K H e τ) := by
  intro F aFS e τ
  let D := fullConstantDegreeData k F (SeparableClosure F)
  let RF := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField D
  have hbase : (RF.residueDegree : ℕ) = 1 := by
    change ((intrinsicFiniteAbstractBase F).residueDegree D : ℕ) = 1
    rw [intrinsicFiniteAbstractBase_eq_base, FiniteAbstractField.base_residueDegree]
    rfl
  have hnormalized : D.normalizedDegree RF τ = D.degree τ.val := by
    apply Multiplicative.ext
    have h := D.residueDegree_nsmul_normalizedDegree RF τ
    rw [hbase, one_nsmul] at h
    exact h
  exact hnormalized.trans (intrinsicFullConstantDegree_eq_ambientFixedField k K H e τ)

/-- The concrete full-constant inertia kernels agree under the existing
intrinsic-to-ambient Galois equivalence, including the finite target field. -/
theorem map_intrinsicConstantExtensionInertia_eq_ambientFixedField
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      ((fullConstantDegreeData k F (SeparableClosure F)).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below).map
          (intrinsicBaseEquivAmbientFixedField K H e).toMonoidHom =
        (fullConstantDegreeData k K (SeparableClosure K)).extensionInertiaWithin
          H.field T.field T.below := by
  intro F aFS E hFE hFEgal e EI
  let DI := fullConstantDegreeData k F (SeparableClosure F)
  let DA := fullConstantDegreeData k K (SeparableClosure K)
  let RA := H.toFiniteResidueAbstractField DA
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  have : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) := T.finite
  have hmem (τ : (intrinsicAbstractBase F).toSubgroup) :
      τ ∈ DI.extensionInertiaWithin (intrinsicAbstractBase F) EI.field EI.below ↔
        ψ τ ∈ DA.extensionInertiaWithin H.field T.field T.below := by
    change (τ ∈ extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below ∧
        τ ∈ DI.fieldInertiaWithin (intrinsicAbstractBase F)) ↔
      (ψ τ ∈ extensionSubgroup H.field T.field T.below ∧
        ψ τ ∈ DA.fieldInertiaWithin H.field)
    have hsub := intrinsicExtensionSubgroup_iff_ambientFixedField
      K H T.field T.below e τ
    have hdegree : DI.degree τ.val = DA.normalizedDegree RA (ψ τ) :=
      intrinsicFullConstantDegree_eq_ambientFixedField k K H e τ
    have hkernel : DA.normalizedDegree RA (ψ τ) = 1 ↔
        ψ τ ∈ DA.fieldInertiaWithin H.field := by
      exact Iff.of_eq (congrArg
        (fun N : Subgroup H.field.toSubgroup => ψ τ ∈ N)
        (DA.normalizedDegree_ker RA))
    have hinertia : τ ∈ DI.fieldInertiaWithin (intrinsicAbstractBase F) ↔
        ψ τ ∈ DA.fieldInertiaWithin H.field := by
      change DI.degree τ.val = 1 ↔ ψ τ ∈ DA.fieldInertiaWithin H.field
      rw [hdegree]
      exact hkernel
    exact and_congr hsub hinertia
  apply Subgroup.ext
  intro σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (hmem τ).mp hτ
  · intro hσ
    refine ⟨ψ.symm σ, (hmem (ψ.symm σ)).mpr ?_, ψ.apply_symm_apply σ⟩
    rw [ψ.apply_symm_apply]
    exact hσ

/-- Continuous transport of the actual constant-inertia quotient from the
separable closure of the fixed field to the original ambient closure. -/
def intrinsicConstantFrobeniusQuotientEquivAmbientFixedField
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      ((intrinsicAbstractBase F).toSubgroup ⧸
        (fullConstantDegreeData k F (SeparableClosure F)).extensionInertiaWithin
          (intrinsicAbstractBase F) EI.field EI.below) ≃ₜ*
        (H.field.toSubgroup ⧸
          (fullConstantDegreeData k K (SeparableClosure K)).extensionInertiaWithin
            H.field T.field T.below) := by
  intro F aFS E hFE hFEgal e EI
  exact LocalFieldTheory.QuotientGroup.continuousCongr _ _
    (intrinsicBaseContinuousEquivAmbientFixedField K H e)
    (map_intrinsicConstantExtensionInertia_eq_ambientFixedField k K H T e)

/-- The quotient transport preserves normalized Frobenius degree. -/
theorem intrinsicConstantFrobeniusQuotientEquivAmbientFixedField_degree
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      let DI := fullConstantDegreeData k F (SeparableClosure F)
      let DA := fullConstantDegreeData k K (SeparableClosure K)
      ∀ q : (intrinsicAbstractBase F).toSubgroup ⧸
          DI.extensionInertiaWithin (intrinsicAbstractBase F) EI.field EI.below,
        DA.extensionNormalizedDegree (H.toFiniteResidueAbstractField DA)
            T.field T.below (intrinsicConstantFrobeniusQuotientEquivAmbientFixedField
              k K H T e q) =
          DI.extensionNormalizedDegree
            ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI)
            EI.field EI.below q := by
  intro F aFS E hFE hFEgal e EI DI DA q
  refine QuotientGroup.induction_on q ?_
  intro τ
  change DA.normalizedDegree (H.toFiniteResidueAbstractField DA)
      (intrinsicBaseEquivAmbientFixedField K H e τ) =
    DI.normalizedDegree ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI) τ
  exact (intrinsicNormalizedDegree_eq_ambientFixedField k K H e τ).symm

/-- A positive Frobenius element is carried to a positive Frobenius element
with the same actual full-constant degree. -/
def intrinsicConstantFrobeniusElementToAmbientFixedField
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      let DI := fullConstantDegreeData k F (SeparableClosure F)
      let DA := fullConstantDegreeData k K (SeparableClosure K)
      DI.FrobeniusElements ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI)
          EI.field EI.below →
        DA.FrobeniusElements (H.toFiniteResidueAbstractField DA) T.field T.below := by
  intro F aFS E hFE hFEgal e EI DI DA σ
  refine ⟨intrinsicConstantFrobeniusQuotientEquivAmbientFixedField k K H T e σ.val, ?_⟩
  rw [intrinsicConstantFrobeniusQuotientEquivAmbientFixedField_degree]
  exact σ.property

/-- The same closure equivalence identifies the subgroups fixing the
Frobenius auxiliary fields. -/
theorem intrinsicConstantFrobeniusFixedSubgroup_mem_iff
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      let DI := fullConstantDegreeData k F (SeparableClosure F)
      let DA := fullConstantDegreeData k K (SeparableClosure K)
      let RI := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI
      let RA := H.toFiniteResidueAbstractField DA
      ∀ (σ : DI.FrobeniusElements RI EI.field EI.below)
        (τ : (intrinsicAbstractBase F).toSubgroup),
        τ ∈ DI.frobeniusFixedSubgroupWithin RI EI.field EI.below σ ↔
          intrinsicBaseEquivAmbientFixedField K H e τ ∈
            DA.frobeniusFixedSubgroupWithin RA T.field T.below
              (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ) := by
  intro F aFS E hFE hFEgal e EI DI DA RI RA σ τ
  let ξ := intrinsicConstantFrobeniusQuotientEquivAmbientFixedField k K H T e
  change QuotientGroup.mk τ ∈
      (closedSubgroupGenerated (Set.range (fun _ : Unit => σ.val))).toSubgroup ↔
    ξ (QuotientGroup.mk τ) ∈
      (closedSubgroupGenerated (Set.range (fun _ : Unit => ξ σ.val))).toSubgroup
  simp only [Set.range_unique]
  constructor
  · intro h
    exact map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom ξ) σ.val h
  · intro h
    exact continuousMulEquiv_preimage_mem_closedSubgroupGenerated_singleton_of_eq
      ξ σ.val (QuotientGroup.mk τ) (ξ σ.val) (ξ (QuotientGroup.mk τ)) rfl rfl h

/-- Membership in the actual Frobenius auxiliary field is preserved by the
chosen separable-closure equivalence. -/
theorem intrinsicConstantFrobeniusFixedField_mem_iff
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
      let DI := fullConstantDegreeData k F (SeparableClosure F)
      let DA := fullConstantDegreeData k K (SeparableClosure K)
      let RI := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI
      let RA := H.toFiniteResidueAbstractField DA
      ∀ σ : DI.FrobeniusElements RI EI.field EI.below,
        let σA := intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ
        let SI := DI.frobeniusFixedField RI EI.field EI.below σ
        let SA := DA.frobeniusFixedField RA T.field T.below σA
        ∀ x : SeparableClosure F,
          x ∈ abstractFixedField F (SeparableClosure F) SI ↔
            e x ∈ abstractFixedField K (SeparableClosure K) SA := by
  intro F aFS E hFE hFEgal e EI DI DA RI RA σ σA SI SA x
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  have hmem := intrinsicConstantFrobeniusFixedSubgroup_mem_iff k K H T e σ
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx ρ hρ
    obtain ⟨a, ha, rfl⟩ :=
      (DA.mem_frobeniusFixedField_iff RA T.field T.below σA ρ).mp hρ
    let τ : (intrinsicAbstractBase F).toSubgroup := ψ.symm a
    have hτ : τ ∈ DI.frobeniusFixedSubgroupWithin RI EI.field EI.below σ := by
      apply (hmem τ).mpr
      change ψ (ψ.symm a) ∈ DA.frobeniusFixedSubgroupWithin RA T.field T.below σA
      rw [ψ.apply_symm_apply]
      exact ha
    have hτSI : τ.val ∈ SI :=
      (DI.mem_frobeniusFixedField_iff RI EI.field EI.below σ τ.val).mpr ⟨τ, hτ, rfl⟩
    calc
      a.val (e x) = (ψ τ).val (e x) := by
        rw [show ψ τ = a from ψ.apply_symm_apply a]
      _ = e (τ.val x) := by
        change e (τ.val (e.symm (e x))) = e (τ.val x)
        rw [e.symm_apply_apply]
      _ = e x := congrArg e (hx τ.val hτSI)
  · intro hx ρ hρ
    obtain ⟨a, ha, rfl⟩ :=
      (DI.mem_frobeniusFixedField_iff RI EI.field EI.below σ ρ).mp hρ
    have hψa : ψ a ∈ DA.frobeniusFixedSubgroupWithin RA T.field T.below σA :=
      (hmem a).mp ha
    have hψaSA : (ψ a).val ∈ SA :=
      (DA.mem_frobeniusFixedField_iff RA T.field T.below σA (ψ a).val).mpr
        ⟨ψ a, hψa, rfl⟩
    have hfix := hx (ψ a).val hψaSA
    change e (a.val (e.symm (e x))) = e x at hfix
    rw [e.symm_apply_apply] at hfix
    exact e.injective hfix

/-- The transported Frobenius class induces the same automorphism of the
finite target field under the two concrete Galois quotient identifications. -/
theorem intrinsicConstantFrobeniusRestriction_eq_ambientFixedField
    (T : FiniteGaloisSubextension H.field) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      fixedBaseClosureAlgebra (K := K) (H := H)
    let E := abstractRelativeFixedField K (SeparableClosure K) T.below
    let _ : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field T.field T.below H.finite T.finite
    let _ : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field T.field T.below T.normal
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let i := e.symm.toAlgHom.comp E.val
      let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
      let DI := fullConstantDegreeData k F (SeparableClosure F)
      let DA := fullConstantDegreeData k K (SeparableClosure K)
      let RI := (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI
      let RA := H.toFiniteResidueAbstractField DA
      ∀ σ : DI.FrobeniusElements RI EI.field EI.below,
        abstractExtensionQuotientEquivGaloisGroup
            K (SeparableClosure K) H.field T.field T.below T.normal
            (DA.frobeniusRestriction RA T.field T.below
              (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) =
          finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E i
            (DI.frobeniusRestriction RI EI.field EI.below σ) := by
  intro F aFS E hFE hFEgal e i EI DI DA RI RA σ
  have : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) := T.finite
  let ξ := intrinsicConstantFrobeniusQuotientEquivAmbientFixedField k K H T e
  let qA := abstractExtensionQuotientEquivGaloisGroup
    K (SeparableClosure K) H.field T.field T.below T.normal
  let qI := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E i
  change qA (DA.extensionRestriction H.field T.field T.below (ξ σ.val)) =
    qI (DI.extensionRestriction (intrinsicAbstractBase F) EI.field EI.below σ.val)
  have hq (q : (intrinsicAbstractBase F).toSubgroup ⧸
      DI.extensionInertiaWithin (intrinsicAbstractBase F) EI.field EI.below) :
      qA (DA.extensionRestriction H.field T.field T.below (ξ q)) =
        qI (DI.extensionRestriction (intrinsicAbstractBase F) EI.field EI.below q) := by
    refine QuotientGroup.induction_on q ?_
    intro τ
    exact fixedFieldQuotientEquiv_mk_compatibility K H T.field T.below e τ
  exact hq σ.val

/-- Positive intrinsic Frobenius elements for the given fixed-base presentation. -/
abbrev intrinsicFixedBaseFrobeniusElements
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K) : Type :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  let DI := fullConstantDegreeData k F (SeparableClosure F)
  DI.FrobeniusElements ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField DI)
    EI.field EI.below

/-- The actual auxiliary field for the chosen intrinsic fixed-base presentation. -/
abbrev fixedBaseFrobeniusAuxiliaryField
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    IntermediateField (abstractFixedField K (SeparableClosure K) H.field)
      (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliaryField k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

-- Fix the concrete source before selecting its shared generic scalar structure.
local instance fixedBaseFrobeniusAuxiliaryCommSemiring
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    CommSemiring (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliaryCommSemiring
    k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

local instance fixedBaseFrobeniusAuxiliaryAlgebra
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    Algebra (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliaryAlgebra k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

local instance fixedBaseFrobeniusAuxiliarySMul
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    SMul (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliarySMul k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

local instance fixedBaseFrobeniusAuxiliaryModule
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    Module (abstractFixedField K (SeparableClosure K) H.field)
      (fixedBaseFrobeniusAuxiliaryField k K H T e σ) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) T.below
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E (e.symm.toAlgHom.comp E.val)
  intrinsicFrobeniusAuxiliaryModule k F (SeparableClosure F) (intrinsicFiniteAbstractBase F) EI σ

attribute [local instance] ambientFrobeniusAuxiliaryAlgebra

/-- The chosen closure equivalence restricts to an algebra equivalence
between the actual Frobenius auxiliary fields. -/
def intrinsicConstantFrobeniusFixedFieldEquivAmbientFixedField
    (T : FiniteGaloisSubextension H.field)
    (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
      ≃ₐ[abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K)
    (σ : intrinsicFixedBaseFrobeniusElements k K H T e) :
    (fixedBaseFrobeniusAuxiliaryField k K H T e σ) ≃ₐ[
      abstractFixedField K (SeparableClosure K) H.field]
      (ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
        (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let LI : IntermediateField F (SeparableClosure F) :=
    fixedBaseFrobeniusAuxiliaryField k K H T e σ
  let LA : IntermediateField F (SeparableClosure K) :=
    ambientFrobeniusAuxiliaryField k K (SeparableClosure K) H T
        (intrinsicConstantFrobeniusElementToAmbientFixedField k K H T e σ)
  have hmap : LI.map e.toAlgHom = LA := by
    apply IntermediateField.ext
    intro x
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (intrinsicConstantFrobeniusFixedField_mem_iff k K H T e σ y).mp hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply (intrinsicConstantFrobeniusFixedField_mem_iff k K H T e σ (e.symm x)).mpr
      rw [e.apply_symm_apply]
      exact hx
  let LM : IntermediateField F (SeparableClosure K) := LI.map e.toAlgHom
  let aFLM : Algebra F LM := LM.algebra
  let eI : LI ≃ₐ[F] LM := IntermediateField.equivMap LI e.toAlgHom
  let eA : LM ≃ₐ[F] LA := IntermediateField.equivOfEq hmap
  exact eI.trans eA

end FunctionField
