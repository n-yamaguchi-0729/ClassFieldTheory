/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.MultiplicativeHilbert90
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.Group.Action.Units

/-!
# Hilbert 90 for finite faithful field actions

The fixed field supplies the actual finite extension. Thus a faithful finite
field action suffices; no auxiliary finite extension is required as input.
-/

noncomputable section

namespace CyclicCohomology

open ProfiniteCohomology.Herbrand

attribute [local instance] Units.mulDistribMulActionRight

variable {G L : Type*} [Group G] [Field L]
    [MulSemiringAction G L] [FaithfulSMul G L]

/-- Noether Hilbert 90 for an actual finite faithful field action. -/
theorem exists_unit_coboundary_of_finite_action [Finite G] (f : G → Lˣ)
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) :
    ∃ y : Lˣ, ∀ g : G, (g • y) / y = f g := by
  let e := FixedPoints.toAlgAutMulEquiv G L
  have he (g : G) (x : Lˣ) : e g • x = g • x := by
    apply Units.ext
    rfl
  have hes (g : L ≃ₐ[FixedPoints.subfield G L] L) (x : Lˣ) :
      e.symm g • x = g • x := by
    rw [← he, e.apply_symm_apply]
  have hf' : groupCohomology.IsMulCocycle₁
      (fun g : L ≃ₐ[FixedPoints.subfield G L] L => f (e.symm g)) := by
    intro g h
    change f (e.symm (g * h)) = g • f (e.symm h) * f (e.symm g)
    rw [map_mul, hf, hes]
  obtain ⟨y, hy⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (fun g : L ≃ₐ[FixedPoints.subfield G L] L => f (e.symm g)) hf'
  refine ⟨y, fun g => ?_⟩
  simpa only [he, e.symm_apply_apply] using hy (e g)

/-- A norm-one unit for a finite faithful cyclic field action has an actual primitive. -/
theorem exists_unit_coboundary_of_finite_action_norm_eq_one [Fintype G]
    (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : Lˣ)
    (hx : tateNorm G Lˣ x = 1) :
    ∃ y : Lˣ, (σ • y) / y = x := by
  obtain ⟨f, hf, hfx⟩ := exists_mulCocycle_of_tateNorm_eq_one σ hσ x hx
  obtain ⟨y, hy⟩ := exists_unit_coboundary_of_finite_action f hf
  exact ⟨y, (hy σ).trans hfx⟩

end CyclicCohomology
