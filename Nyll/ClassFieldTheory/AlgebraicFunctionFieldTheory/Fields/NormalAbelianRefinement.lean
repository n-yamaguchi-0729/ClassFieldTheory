/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Basic
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension

/-!
# Ambient normal refinements of relative abelian extensions

The ambient normal core of a finite-index subgroup remains finite index.
When the base subgroup is normal, its commutator subgroup is normal in the
ambient group. Consequently taking the ambient normal core of a relative
abelian extension preserves abelianity over the same base.

Thus the finite relative abelian extensions which are also normal over the
original base are cofinal. This supplies the actual finite stages required
to pass the native Artin transfer square to a constant extension.
-/

@[expose] public section

noncomputable section

open scoped commutatorElement

namespace FunctionField

section Groups

variable {G : Type*} [Group G]

/-- An ambient normal core preserves a relative abelian quotient over a
normal base subgroup. -/
theorem quotient_subgroupOf_normalCore_isMulCommutative
    (H U : Subgroup G) [H.Normal] [(U.subgroupOf H).Normal]
    [IsMulCommutative (H ⧸ U.subgroupOf H)] :
    IsMulCommutative (H ⧸ U.normalCore.subgroupOf H) := by
  have hcomm : commutator H ≤ U.subgroupOf H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hambient : ⁅H, H⁆ ≤ U := by
    rw [← H.map_subtype_commutator]
    exact Subgroup.map_le_iff_le_comap.mpr hcomm
  have hcore : ⁅H, H⁆ ≤ U.normalCore :=
    Subgroup.normal_le_normalCore.mpr hambient
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  apply Subgroup.map_le_iff_le_comap.mp
  rw [H.map_subtype_commutator]
  exact hcore

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ambient normal core of a closed subgroup is closed, as the
intersection of its original conjugates. -/
theorem isClosed_normalCore_of_isClosed (U : Subgroup G)
    (hU : IsClosed (U : Set G)) :
    IsClosed (U.normalCore : Set G) := by
  have hset : (U.normalCore : Set G) =
      ⋂ b : G, (fun a : G => b * a * b⁻¹) ⁻¹' (U : Set G) := by
    ext a
    change (∀ b : G, b * a * b⁻¹ ∈ U) ↔ _
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [hset]
  exact isClosed_iInter fun b =>
    hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end Groups

end FunctionField

namespace ClassFormation

open KummerTheory CyclicCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
private theorem finiteAbstractField_ambientQuotient_finite (H : FiniteAbstractField G) :
    Finite (G ⧸ H.field.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.field.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (extensionSubgroup (baseField G) H.field (le_baseField H.field)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite (baseField G).toSubgroup _
    (extensionSubgroup (baseField G) H.field (le_baseField H.field)) H.finite

namespace FiniteGaloisSubextension

/-- The actual ambient normal core gives a finite Galois refinement of a
finite relative extension. -/
def normalRefinement (H : FiniteAbstractField G)
    (T : FiniteGaloisSubextension H.field) : FiniteGaloisSubextension H.field where
  field :=
    { toSubgroup := T.field.toSubgroup.normalCore
      isClosed' := FunctionField.isClosed_normalCore_of_isClosed
        T.field.toSubgroup T.field.isClosed' }
  below := T.field.toSubgroup.normalCore_le.trans T.below
  normal := by
    change (T.field.toSubgroup.normalCore.subgroupOf H.field.toSubgroup).Normal
    infer_instance
  finite := by
    have hfinite : Finite (G ⧸ T.field.toSubgroup) :=
      finiteAbstractField_ambientQuotient_finite T.toFiniteAbstractFieldExtension.field
    have hindex : T.field.toSubgroup.FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    change Finite (H.field.toSubgroup ⧸
      T.field.toSubgroup.normalCore.subgroupOf H.field.toSubgroup)
    infer_instance

/-- The constructed refinement is normal over the original ambient base. -/
theorem normalRefinement_normal (H : FiniteAbstractField G)
    (T : FiniteGaloisSubextension H.field) :
    (normalRefinement H T).field.toSubgroup.Normal :=
  T.field.toSubgroup.normalCore_normal

/-- The new finite stage contains the old extension field. -/
theorem normalRefinement_le (H : FiniteAbstractField G)
    (T : FiniteGaloisSubextension H.field) :
    (normalRefinement H T).field.toSubgroup ≤ T.field.toSubgroup :=
  T.field.toSubgroup.normalCore_le

/-- Over a normal base, refinement by the ambient normal core preserves
the actual abelian relative Galois group. -/
theorem normalRefinement_isMulCommutative (H : FiniteAbstractField G)
    [H.field.toSubgroup.Normal] (T : FiniteGaloisSubextension H.field)
    [IsMulCommutative T.extensionQuotient] :
    IsMulCommutative (normalRefinement H T).extensionQuotient := by
  have hnormal : (T.field.toSubgroup.subgroupOf H.field.toSubgroup).Normal := T.normal
  have hcomm : IsMulCommutative
      (H.field.toSubgroup ⧸ T.field.toSubgroup.subgroupOf H.field.toSubgroup) :=
    inferInstanceAs (IsMulCommutative T.extensionQuotient)
  change IsMulCommutative
    (H.field.toSubgroup ⧸ T.field.toSubgroup.normalCore.subgroupOf H.field.toSubgroup)
  exact FunctionField.quotient_subgroupOf_normalCore_isMulCommutative
    H.field.toSubgroup T.field.toSubgroup

/-- Actual ambient-normal finite abelian stages are cofinal among all
relative finite abelian stages over a normal finite base. -/
theorem exists_normal_abelian_refinement (H : FiniteAbstractField G)
    [H.field.toSubgroup.Normal] (T : FiniteGaloisSubextension H.field)
    [IsMulCommutative T.extensionQuotient] :
    ∃ U : FiniteGaloisSubextension H.field,
      U.field.toSubgroup.Normal ∧ IsMulCommutative U.extensionQuotient ∧
        U.field.toSubgroup ≤ T.field.toSubgroup :=
  ⟨normalRefinement H T, normalRefinement_normal H T,
    normalRefinement_isMulCommutative H T, normalRefinement_le H T⟩

end FiniteGaloisSubextension

end ClassFormation
