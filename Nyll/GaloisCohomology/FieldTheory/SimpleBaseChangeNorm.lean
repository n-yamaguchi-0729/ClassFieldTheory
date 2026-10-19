/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.CompositumNorm
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Norms in simple extensions with unchanged minimal polynomial

Equality of minimal polynomials under the specified scalar embedding gives
equality of the actual field norms in the common ambient field.
-/

noncomputable section

namespace FieldTheory

open IntermediateField

/-- Preserving the minimal polynomial preserves norms in the generated simple extension. -/
theorem norm_adjoin_simple_baseChange
    {B A Ω : Type*} [Field B] [Field A] [Field Ω]
    [Algebra B A] [Algebra B Ω] [Algebra A Ω] [IsScalarTower B A Ω]
    (α : Ω) (hα : IsIntegral B α)
    (hmin : (minpoly B α).map (algebraMap B A) = minpoly A α)
    (x : Ω) (hxB : x ∈ adjoin B {α}) (hxA : x ∈ adjoin A {α}) :
    algebraMap A Ω (Algebra.norm A (⟨x, hxA⟩ : adjoin A {α})) =
      algebraMap B Ω (Algebra.norm B (⟨x, hxB⟩ : adjoin B {α})) := by
  let E := adjoin B ({α} : Set Ω)
  let L := adjoin A ({α} : Set Ω)
  have hle : E ≤ L.restrictScalars B :=
    adjoin_le_iff.mpr (fun y hy => subset_adjoin A ({α} : Set Ω) hy)
  let f : E →ₐ[B] L := inclusion hle
  let : Algebra E L := f.toAlgebra
  have : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq (fun y => (f.commutes y).symm)
  have hfinE : FiniteDimensional B E := adjoin.finiteDimensional hα
  have hfinL : FiniteDimensional A L := adjoin.finiteDimensional hα.tower_top
  have hgen : Algebra.adjoin A (Set.range (algebraMap E L)) = ⊤ := by
    apply top_unique
    rw [← (adjoin.powerBasis (hα.tower_top (A := A))).adjoin_gen_eq_top]
    apply Algebra.adjoin_mono
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨AdjoinSimple.gen B α, rfl⟩
  have hdeg : Module.finrank A L = Module.finrank B E := by
    rw [adjoin.finrank hα.tower_top, adjoin.finrank hα, ← hmin, Polynomial.natDegree_map]
  have hnorm := norm_algebraMap_of_generated_of_finrank_eq B E A L hgen hdeg
    (⟨x, hxB⟩ : E)
  have h := congrArg (algebraMap A Ω) hnorm
  rw [← IsScalarTower.algebraMap_apply B A Ω] at h
  exact h

end FieldTheory
