/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityQuotientEquivOfArtin
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The local norm quotient is induced by the Artin map

The existence statements for the finite Artin map and the norm-quotient
isomorphism alone do not say that their witnesses agree. Here a single
canonical Artin map is chosen, and its quotient isomorphism is characterized
uniquely by its values on classes of nonzero field elements.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The continuous norm-quotient equivalence is uniquely determined by the
canonical finite local Artin map, with the expected value on every class. -/
theorem finiteAbelianLocalReciprocity_quotientEquiv_mk
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      artin.ker = fieldNormSubgroup K L ∧
      ∃! e : FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L),
        ∀ x : Kˣ, e (QuotientGroup.mk' (fieldNormSubgroup K L) x) = artin x := by
  exact ⟨LocalClassFieldTheory.Universe.abelianLocalArtinMap K L,
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_surjective K L,
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_ker K L,
    LocalClassFieldTheory.Universe.quotientEquiv_existsUnique K L⟩

end ClassFieldTheory
