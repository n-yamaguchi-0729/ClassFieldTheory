/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseInertia
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

/-!
# The actual conductor-zero criterion in independent field universes

The conductor remains the least depth in the original norm subgroup. Its depth-zero condition
is equivalent to triviality of the actual residue inertia, whose order is the ramification index.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

universe u v

/-- The original norm conductor is zero exactly when the actual valued extension is unramified. -/
theorem isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] :
    IsUnramifiedValuedExtension K L ↔ localConductorExponent K L = 0 := by
  have hnorm : (abelianLocalArtinMonoidHom K L).ker = localNormSubgroup K L :=
    abelianLocalArtinMap_ker K L
  rw [localConductorExponent_eq_zero_iff, ← hnorm, ← Subgroup.map_eq_bot_iff,
    abelianLocalArtinMonoidHom_units_eq_residue_ker]
  constructor
  · intro h
    let : IsUnramifiedValuedExtension K L := h
    exact (MonoidHom.ker_eq_bot_iff _).mpr
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L)
  · intro h
    refine ⟨?_⟩
    rw [← galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L, h]
    exact Subgroup.card_bot

end LocalClassFieldTheory.Universe
