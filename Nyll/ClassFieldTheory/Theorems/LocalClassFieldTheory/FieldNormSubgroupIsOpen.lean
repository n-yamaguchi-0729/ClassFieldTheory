/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin

/-!
# Openness of the local norm subgroup

For a finite abelian extension of a nonarchimedean local field, the subgroup
of nonzero field norms is open in the multiplicative group of the base.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- The norm subgroup of a finite abelian local extension is open. -/
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

end ClassFieldTheory
