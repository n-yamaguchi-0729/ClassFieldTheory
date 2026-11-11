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
# Index formula in finite abelian local reciprocity

The index of the norm subgroup equals the degree of the finite abelian local
extension.  This is the numerical form of the reciprocity isomorphism.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- The norm-subgroup index is the degree of the extension. -/
theorem fieldNormSubgroup_index_eq_finrank
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).index = Module.finrank K L := by
  let e := Classical.choose
    (LocalClassFieldTheory.Universe.quotientEquiv_existsUnique K L).exists
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr e.toEquiv).trans (IsGalois.card_aut_eq_finrank K L)

end ClassFieldTheory
