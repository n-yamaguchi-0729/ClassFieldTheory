/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierBoundedClasses
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.RiemannRoch
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.RiemannGenusReachedAtEq

/-!
# Large bounded Artin–Schreier parameter spaces

An actual effective divisor bound is supplied by Riemann–Roch. Beyond this
bound the number of AS classes depends only on the difference of degrees.
Neither a genus witness nor the full constant field is an extra input.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K : Type*) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Above an actual effective bound, bounded AS classes have the expected
degree-counting cardinality. -/
theorem exists_bound_card_boundedArtinSchreierClasses :
    ∃ D₀ : Divisor k K, 0 ≤ D₀ ∧ ∀ D : Divisor k K, D₀ ≤ D →
      Nat.card (boundedArtinSchreierClasses p (p • D)) =
        p * Nat.card k ^ (Divisor.degree (p • D) - Divisor.degree D).toNat := by
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hess : Algebra.EssFiniteType k K := essFiniteType k K
  have hplace : Nonempty (Place k K) := nonempty_place k K
  have hzero : FiniteDimensional k (LSpace (0 : Divisor k K)) :=
    finiteDimensional_lSpace_zero k K
  obtain ⟨γ, B, hB⟩ := exists_genusReached (k := k) (K := K)
  refine ⟨B ⊔ 0, le_sup_right, ?_⟩
  intro D hD
  have hDnonneg : 0 ≤ D := le_sup_right.trans hD
  have hBD : B ≤ D := le_sup_left.trans hD
  have hDpD : D ≤ p • D := by
    intro v
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have hDv : 0 ≤ D v := hDnonneg v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hDv
  have hellD := hB.eq_of_ge hBD
  have hellpD := hB.eq_of_ge (hBD.trans hDpD)
  have hdiff : ell (p • D) - ell D =
      (Divisor.degree (p • D) - Divisor.degree D).toNat := by omega
  rw [card_boundedArtinSchreierClasses p D hDnonneg, hdiff]

end FunctionField
