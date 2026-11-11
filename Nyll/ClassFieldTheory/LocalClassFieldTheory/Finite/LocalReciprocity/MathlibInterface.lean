/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.Classification
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConjugationNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-!
# Mathlib-facing finite local class field theory

This is the implementation layer for the reader-facing local CFT module.
It collects the existing finite, absolute, naturality, normalization, and
existence results without renaming them or wrapping them in an existence
structure.

The finite reciprocity and norm-subgroup statements allow independent field
universes and use the specified Artin map. The abstract-existence statements
retain the native class-formation model used by their classification source.
-/



@[expose] public section

noncomputable section

namespace ClassFieldTheory.LocalCFT

universe u v

open ClassFormation

noncomputable local instance localNormQuotientTopologicalSpace
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (LocalFieldTheory.NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ LocalFieldTheory.localNormSubgroup K L)
  infer_instance

noncomputable local instance fieldNormQuotientTopologicalSpace
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [TopologicalSpace K] :
    TopologicalSpace (FieldNormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ fieldNormSubgroup K L)
  infer_instance

/-- Finite abelian local extensions are classified, contravariantly, by
open finite-index subgroups of `Kˣ`. -/
theorem finiteAbelianLocalExistence
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∀ H : LocalClassFieldTheory.OpenFiniteIndexSubgroup K,
      ∃ L : FiniteAbelianSubextension
          (LocalClassFieldTheory.intrinsicAbstractBase K),
        LocalClassFieldTheory.finiteAbelianNormSubgroupMap K L = H :=
  LocalClassFieldTheory.finiteAbelianNormSubgroupMap_surjective K

/-- Order-isomorphism form of the finite abelian local existence theorem. -/
theorem finiteAbelianLocalExistence_orderIso
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FiniteAbelianSubextension
          (LocalClassFieldTheory.intrinsicAbstractBase K) ≃o
        (LocalClassFieldTheory.OpenFiniteIndexSubgroup K)ᵒᵈ) :=
  ⟨LocalClassFieldTheory.finiteAbelianNormSubgroupOrderIso K⟩

/-- Construction of the Artin map in the finite abelian local reciprocity
theorem, expressed only through its mathematical universal properties. -/
theorem finiteAbelianLocalReciprocity
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      ∀ x : Kˣ, artin x = 1 ↔ IsFieldNorm K L x := by
  refine ⟨LocalClassFieldTheory.Universe.abelianLocalArtinMap K L,
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_surjective K L, ?_⟩
  intro x
  change x ∈ (LocalClassFieldTheory.Universe.abelianLocalArtinMap K L).toMonoidHom.ker ↔
    x ∈ fieldNormSubgroup K L
  rw [LocalClassFieldTheory.Universe.abelianLocalArtinMap_ker]

/-- The quotient form of finite abelian local reciprocity. -/
theorem finiteAbelianLocalReciprocity_quotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L)) := by
  obtain ⟨e, _, _⟩ := LocalClassFieldTheory.Universe.quotientEquiv_existsUnique K L
  exact ⟨e⟩

/-- The field-norm subgroup is open in the native topology on `Kˣ`. -/
theorem isOpen_fieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (fieldNormSubgroup K L : Set Kˣ) := by
  rw [← LocalClassFieldTheory.Universe.abelianLocalArtinMap_ker K L]
  exact (isOpen_discrete ({1} : Set Gal(L/K))).preimage
    (LocalClassFieldTheory.Universe.abelianLocalArtinMap K L).continuous_toFun

/-- The field-norm subgroup has finite index, by finite local reciprocity. -/
theorem fieldNormSubgroup_finiteIndex
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).FiniteIndex := by
  let : Finite (L ≃ₐ[K] L) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  obtain ⟨e⟩ := finiteAbelianLocalReciprocity_quotient K L
  let : Finite (FieldNormQuotient K L) :=
    Finite.of_equiv (L ≃ₐ[K] L) e.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The norm-subgroup index equals the degree of the abelian extension. -/
theorem fieldNormSubgroup_index_eq_finrank
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).index = Module.finrank K L := by
  obtain ⟨e⟩ := finiteAbelianLocalReciprocity_quotient K L
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr e.toEquiv).trans (IsGalois.card_aut_eq_finrank K L)

end ClassFieldTheory.LocalCFT
