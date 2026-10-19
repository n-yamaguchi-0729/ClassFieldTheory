/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionResidue

/-!
# Constant Frobenius powers fixing actual places

In a degree-`n` extension of the full constants, the decomposition group at a
place above a degree-`d` place has index `gcd(n,d)`. The global Galois group is
cyclic, so the `d`th power of every automorphism fixes that place. This applies
in particular to the arithmetic Frobenius constructed in the actual constant
extension.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve
open scoped AlgebraicCurve.Place

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]

/-- The decomposition-group index in the actual constant extension is the
gcd of the extension degree and the degree of the place below. -/
theorem decompositionGroup_index_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n)) :
    (IdeleGroup.decompositionGroup (K := K) w).index =
      Nat.gcd n (w.restrict K).deg := by
  let D := IdeleGroup.decompositionGroup (K := K) w
  have hindex : D.index * Nat.card D =
      Module.finrank K (fullConstantDegreeStage k K Ω n) :=
    D.index_mul_card.trans (IsGalois.card_aut_eq_finrank K (fullConstantDegreeStage k K Ω n))
  have hfiber := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
    (w.restrict K) w rfl
  rw [← IdeleGroup.decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg] at hfiber
  have hcard : Nat.card D ≠ 0 := Nat.ne_of_gt (Nat.card_pos (α := D))
  have hindexFiber : D.index =
      ((w.restrict K).fiberOver (fullConstantDegreeStage k K Ω n)).card :=
    mul_right_cancel₀ hcard (hindex.trans hfiber.symm)
  exact hindexFiber.trans (card_fiberOver_fullConstantDegreeStage k K Ω n w)

/-- Every global automorphism raised to the degree of the place below belongs
to the actual decomposition group of a constant extension. -/
theorem pow_degree_mem_decompositionGroup_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n))
    (σ : fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :
    σ ^ (w.restrict K).deg ∈ IdeleGroup.decompositionGroup (K := K) w := by
  have : IsCyclic
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :=
    isCyclic_fullConstantDegreeStage k K Ω n
  let D := IdeleGroup.decompositionGroup (K := K) w
  have hpow : σ ^ Nat.gcd n (w.restrict K).deg ∈ D := by
    rw [← decompositionGroup_index_fullConstantDegreeStage k K Ω n w]
    exact D.pow_index_mem σ
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right n (w.restrict K).deg
  rw [hm, pow_mul]
  exact D.pow_mem hpow m

/-- Arithmetic constant Frobenius raised to the degree of the place below
fixes the actual place of the degree-`n` constant extension. -/
theorem fullConstantDegreeFrobenius_pow_degree_smul_place (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n)) :
    SemilinearAut.ofAlgAut
        (((fullConstantDegreeFrobenius k K Ω n) ^ (w.restrict K).deg).restrictScalars
          (algebraicClosure k K)) • w = w :=
  IdeleGroup.decompositionGroup_smul_eq w
    ⟨(fullConstantDegreeFrobenius k K Ω n) ^ (w.restrict K).deg,
      pow_degree_mem_decompositionGroup_fullConstantDegreeStage k K Ω n w
        (fullConstantDegreeFrobenius k K Ω n)⟩

end FunctionField
