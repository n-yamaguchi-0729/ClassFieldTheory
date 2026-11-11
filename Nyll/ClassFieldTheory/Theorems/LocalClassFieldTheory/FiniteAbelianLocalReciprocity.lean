/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Finite abelian local reciprocity

This module states local reciprocity for a finite abelian extension `L / K`
of a nonarchimedean local field.  The assumptions provide the finite
abelian-Galois extension together with the valuative topology on `K`.  The
conclusion supplies a surjective continuous homomorphism from `Kˣ` to the
Galois group whose kernel consists exactly of nonzero field norms from `L`.

This finite quotient statement deliberately leaves the usual uniformizer
normalization and tower functoriality to separate compatibility theorems; it
does not claim that the displayed witness is uniquely determined.
The witness is the existing universe-polymorphic Artin map; its native
comparison identifies it with the original map on fields in `Type 0`.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A finite abelian local extension has a surjective continuous Artin map
whose kernel is its field-norm subgroup. -/
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

end ClassFieldTheory
