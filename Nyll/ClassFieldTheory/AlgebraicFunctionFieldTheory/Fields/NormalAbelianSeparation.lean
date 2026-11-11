/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.NormalAbelianRefinement
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeTransferCoordinates
public import Nyll.ProCGroups.Profinite.Basic

/-!
# Separation by ambient-normal relative abelian fixed fields

The normal-core refinement is enough to detect every element of the
topological abelianization of a finite normal subgroup. An open finite
abelian quotient pulls back to a closed relative subgroup. Its ambient
normal core remains relatively abelian and is contained in that pullback.

For actual Galois groups, the original quotient-to-fixed-field action
then gives joint injectivity of the native finite Artin projections.
-/

@[expose] public section

universe v w

noncomputable section

namespace ClassFormation

open ProCGroups.Abelian KummerTheory CyclicCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (H : FiniteAbstractField G) [H.field.toSubgroup.Normal]
    [CompactSpace H.field.toSubgroup]
    [TotallyDisconnectedSpace (TopologicalAbelianization H.field.toSubgroup)]

/-- The actual ambient-normal relative abelian finite quotients separate
representatives in the topological abelianization of the original subgroup. -/
theorem topologicalAbelianization_mk_eq_of_normal_abelian
    (σ τ : H.field.toSubgroup)
    (h : ∀ T : FiniteGaloisSubextension H.field,
      T.field.toSubgroup.Normal → IsMulCommutative T.extensionQuotient →
        T.extensionQuotientMk σ = T.extensionQuotientMk τ) :
    TopologicalAbelianization.mk H.field.toSubgroup σ =
      TopologicalAbelianization.mk H.field.toSubgroup τ := by
  apply inv_mul_eq_one.mp
  apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
  intro M
  let V : Subgroup H.field.toSubgroup :=
    M.toSubgroup.comap (TopologicalAbelianization.mk H.field.toSubgroup)
  have hVopen : IsOpen (V : Set H.field.toSubgroup) :=
    M.isOpen'.preimage (TopologicalAbelianization.mkₜ H.field.toSubgroup).continuous_toFun
  have hVclosed : IsClosed (V : Set H.field.toSubgroup) :=
    Subgroup.isClosed_of_isOpen V hVopen
  have hVnormal : V.Normal := by
    change (M.toSubgroup.comap (TopologicalAbelianization.mk H.field.toSubgroup)).Normal
    infer_instance
  have hVfinite : Finite (H.field.toSubgroup ⧸ V) :=
    Subgroup.quotient_finite_of_isOpen V hVopen
  have hcomm : commutator H.field.toSubgroup ≤ V := by
    intro ρ hρ
    change TopologicalAbelianization.mk H.field.toSubgroup ρ ∈ M.toSubgroup
    rw [TopologicalAbelianization.mk_eq_one_iff.mpr
      (Subgroup.le_topologicalClosure (commutator H.field.toSubgroup) hρ)]
    exact M.one_mem
  have hVcomm : IsMulCommutative (H.field.toSubgroup ⧸ V) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let S : Subgroup G := V.map H.field.toSubgroup.subtype
  have hSclosed : IsClosed (S : Set G) :=
    (hVclosed.isCompact.image continuous_subtype_val).isClosed
  have hSH : S ≤ H.field.toSubgroup := by
    rintro ρ ⟨ρ', _, rfl⟩
    exact ρ'.property
  have hsub : S.subgroupOf H.field.toSubgroup = V := by
    apply Subgroup.ext
    intro ρ
    constructor
    · rintro ⟨ρ', hρ', heq⟩
      exact (Subtype.ext heq : ρ' = ρ) ▸ hρ'
    · intro hρ
      exact ⟨ρ, hρ, rfl⟩
  have hSnormal : (S.subgroupOf H.field.toSubgroup).Normal := by
    rw [hsub]
    exact hVnormal
  let T : FiniteGaloisSubextension H.field :=
    { field := { toSubgroup := S, isClosed' := hSclosed }
      below := hSH
      normal := hSnormal
      finite := by
        change Finite (H.field.toSubgroup ⧸ S.subgroupOf H.field.toSubgroup)
        rw [hsub]
        exact hVfinite }
  have hTcomm : IsMulCommutative T.extensionQuotient := by
    change IsMulCommutative (H.field.toSubgroup ⧸ S.subgroupOf H.field.toSubgroup)
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    rw [hsub]
    exact hcomm
  let U := FiniteGaloisSubextension.normalRefinement H T
  have hUnormal : U.field.toSubgroup.Normal :=
    FiniteGaloisSubextension.normalRefinement_normal H T
  have hUcomm : IsMulCommutative U.extensionQuotient :=
    FiniteGaloisSubextension.normalRefinement_isMulCommutative H T
  have hUeq := congrArg U.extensionQuotientMulEquiv (h U hUnormal hUcomm)
  rw [U.extensionQuotientMk_apply, U.extensionQuotientMk_apply] at hUeq
  have hUmem : σ⁻¹ * τ ∈ extensionSubgroup H.field U.field U.below :=
    QuotientGroup.eq.mp hUeq
  have hSmem : (σ⁻¹ * τ).val ∈ S :=
    FiniteGaloisSubextension.normalRefinement_le H T
      ((mem_extensionSubgroup_iff H.field U.field U.below (σ⁻¹ * τ)).mp hUmem)
  have hVmem : σ⁻¹ * τ ∈ V := by
    rw [← hsub]
    exact hSmem
  change TopologicalAbelianization.mk H.field.toSubgroup (σ⁻¹ * τ) ∈ M.toSubgroup at hVmem
  simpa only [map_mul, map_inv] using hVmem

end ClassFormation

namespace FunctionField

open ClassFormation LocalClassFieldTheory ProCGroups.Abelian

variable (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (H : FiniteAbstractField Gal(Ω/K)) [H.field.toSubgroup.Normal]

/-- The original finite fixed-field projections normal over the original
base jointly detect the entire actual subgroup abelianization. -/
theorem fixedFieldFiniteArtinProjection_ext
    (x y : TopologicalAbelianization H.field.toSubgroup)
    (h : ∀ (T : FiniteGaloisSubextension H.field),
      ∀ [T.field.toSubgroup.Normal] [IsMulCommutative T.extensionQuotient],
        fixedFieldFiniteArtinProjection K Ω H T x =
          fixedFieldFiniteArtinProjection K Ω H T y) : x = y := by
  have hcompact : CompactSpace H.field.toSubgroup :=
    isCompact_iff_compactSpace.mp H.field.isClosed'.isCompact
  have htd : TotallyDisconnectedSpace (TopologicalAbelianization H.field.toSubgroup) :=
    Homeomorph.totallyDisconnectedSpace
      (fixedFieldAbsoluteAbelianEquiv K Ω H).toHomeomorph
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk H.field.toSubgroup x
  obtain ⟨τ, rfl⟩ := TopologicalAbelianization.surjective_mk H.field.toSubgroup y
  apply topologicalAbelianization_mk_eq_of_normal_abelian H σ τ
  intro T hnormal hcomm
  have hnormal' : T.field.toSubgroup.Normal := hnormal
  have hcomm' : IsMulCommutative T.extensionQuotient := hcomm
  let e := T.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal)
  have he (ρ : H.field.toSubgroup) : e (T.extensionQuotientMk ρ) =
      fixedFieldSubgroupFiniteRestriction K Ω H T ρ := by
    apply AlgEquiv.ext
    intro a
    apply (algebraMap (abstractRelativeFixedField K Ω T.below) Ω).injective
    exact (fixedFieldQuotientGaloisEquiv_mk_commutes K Ω H.field T.field T.below ρ a).trans
      (fixedFieldSubgroupFiniteRestriction_commutes K Ω H T ρ a).symm
  apply e.injective
  rw [he, he]
  exact h T

end FunctionField
