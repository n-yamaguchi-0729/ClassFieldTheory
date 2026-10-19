/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.DecompositionHilbert90
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor
import Nyll.GaloisCohomology.Cyclic.TateH0.Main
import Nyll.GaloisCohomology.Cyclic.Herbrand.Permutation.Module

/-!
# Herbrand quotients at actual function-field completions

The actual decomposition group is the completed Galois group. Local reciprocity
therefore computes the degree-zero Tate quotient of its completed field units.
Hilbert 90 supplies degree minus one.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped AlgebraicCurve.Place

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Actual decomposition-group degree-zero Tate cohomology is the completed norm quotient. -/
def decompositionHerbrandH0EquivNormQuotient (w : Place k L) :
    HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionˣ ≃
      LocalFieldTheory.NormQuotient (w.restrict K).adicCompletion w.adicCompletion :=
  (herbrandH0CompMulEquiv (A := w.adicCompletionˣ)
      (decompositionCompletionEquiv (K := K) w)).toEquiv.trans
    ((herbrandH0EquivTateCohomologyZero (w.restrict K).adicCompletion w.adicCompletion).trans
      (H0TateUnitsIsoNormQuotient (w.restrict K).adicCompletion
        w.adicCompletion).toLinearEquiv.toEquiv)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [IsCyclic (L ≃ₐ[K] L)]

/-- The actual local norm quotient has the order of the actual decomposition group. -/
theorem decomposition_herbrandH0_card (w : Place k L) :
    Nat.card (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionˣ) =
      Nat.card (decompositionGroup (K := K) w) := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have : IsAbelianGalois (w.restrict K).adicCompletion w.adicCompletion :=
    { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }
  rw [Nat.card_congr (decompositionHerbrandH0EquivNormQuotient (K := K) w),
    card_normQuotient_eq_finrank_of_isAbelianGalois]
  exact (decompositionGroup_card_eq_completion_finrank (K := K) w).symm

/-- The local decomposition-group degree-zero Tate quotient is finite. -/
theorem decomposition_herbrandH0_finite (w : Place k L) :
    Finite (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionˣ) := by
  apply Nat.finite_of_card_ne_zero
  rw [decomposition_herbrandH0_card]
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

/-- The field-unit Herbrand quotient at an actual place is its decomposition-group order. -/
theorem decomposition_fieldUnits_herbrandQuotient (w : Place k L)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    let _ : Finite (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionˣ) :=
      decomposition_herbrandH0_finite w
    let _ : Subsingleton
        (HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionˣ σ) :=
      decomposition_herbrandHMinusOne_subsingleton w σ hσ
    herbrandQuotient (G := decompositionGroup (K := K) w) (A := w.adicCompletionˣ) σ =
      (Nat.card (decompositionGroup (K := K) w) : ℚ) := by
  intro h0 hm
  rw [herbrandQuotient_eq_card_ratio, decomposition_herbrandH0_card,
    Nat.card_unique (α :=
      HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionˣ σ),
    Nat.cast_one, div_one]

end FunctionField.IdeleGroup
