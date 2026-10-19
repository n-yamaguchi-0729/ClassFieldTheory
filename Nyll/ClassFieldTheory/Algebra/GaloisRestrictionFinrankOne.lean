/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Galois groups after a degree-one change of the base

Restriction of scalars is an isomorphism when the intermediate base field
has degree one. Every automorphism over the smaller base fixes the larger
base because each of its elements is an actual scalar.
-/

noncomputable section

namespace ClassFieldTheory

variable {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

/-- Restriction is bijective when the scalar extension has degree one. -/
theorem galoisRestrictScalars_bijective_of_finrank_one (h : Module.finrank K F = 1) :
    Function.Bijective (AlgEquiv.restrictScalarsHom K : Gal(E/F) →* Gal(E/K)) := by
  constructor
  · intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun g : Gal(E/K) => g x) hστ
  · intro σ
    have hfix (x : F) : σ (algebraMap F E x) = algebraMap F E x := by
      obtain ⟨a, rfl⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 x
      rw [← IsScalarTower.algebraMap_apply K F E, σ.commutes]
    let τ : Gal(E/F) := { σ.toRingEquiv with commutes' := hfix }
    refine ⟨τ, ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

/-- The actual Galois-group isomorphism induced by restriction of degree-one scalars. -/
def galoisRestrictScalarsEquivOfFinrankOne (h : Module.finrank K F = 1) :
    Gal(E/F) ≃* Gal(E/K) :=
  MulEquiv.ofBijective (AlgEquiv.restrictScalarsHom K)
    (galoisRestrictScalars_bijective_of_finrank_one h)

/-- The forward map of the degree-one equivalence is scalar restriction. -/
@[simp]
theorem galoisRestrictScalarsEquivOfFinrankOne_apply
    (h : Module.finrank K F = 1) (σ : Gal(E/F)) :
    galoisRestrictScalarsEquivOfFinrankOne h σ = σ.restrictScalars K := rfl

end ClassFieldTheory
