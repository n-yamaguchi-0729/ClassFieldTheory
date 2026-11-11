/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Order classification in finite abelian local existence

This module states the classification form of local existence for a
nonarchimedean local field `K`.  Finite abelian intermediate fields of
`SeparableClosure K` are ordered by field inclusion, whereas open
finite-index subgroups of `Kˣ` are ordered contravariantly.  The statement
also records that the order isomorphism sends each extension to its actual
field-norm subgroup.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u

/-- Finite abelian local extensions correspond contravariantly to open
finite-index norm subgroups. -/
theorem finiteAbelianLocalExistence_orderIso
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
  ∃ e : FiniteAbelianLocalExtension K ≃o
        (OpenFiniteIndexSubgroup K)ᵒᵈ,
      ∀ E : FiniteAbelianLocalExtension K,
        (OrderDual.ofDual (e E)).1 = E.normSubgroup := by
  exact ⟨LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K,
    LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply K⟩

/-- The existing classification sends an actual finite extension to the
kernel of its specified general local Artin map. -/
theorem finiteAbelianLocalExistence_orderIso_artinKernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (E : FiniteAbelianLocalExtension K) :
    (OrderDual.ofDual
      (LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K E)).1 =
        (LocalClassFieldTheory.Universe.abelianLocalArtinMap K E.1).toMonoidHom.ker :=
  (LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply K E).trans
    (LocalClassFieldTheory.Universe.abelianLocalArtinMap_ker K E.1).symm

/-- The field selected by the same order isomorphism has Artin kernel
exactly the original open finite-index subgroup. -/
theorem finiteAbelianLocalExistence_orderIso_symm_artinKernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (H : OpenFiniteIndexSubgroup K) :
    let E := (LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K).symm
      (OrderDual.toDual H)
    (LocalClassFieldTheory.Universe.abelianLocalArtinMap K E.1).toMonoidHom.ker = H.1 := by
  intro E
  rw [← finiteAbelianLocalExistence_orderIso_artinKernel K E]
  exact congrArg (fun J : (OpenFiniteIndexSubgroup K)ᵒᵈ => (OrderDual.ofDual J).1)
    ((LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K).apply_symm_apply
      (OrderDual.toDual H))

end ClassFieldTheory
