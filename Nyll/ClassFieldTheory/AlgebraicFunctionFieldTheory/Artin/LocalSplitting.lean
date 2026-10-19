/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.AlgebraicCurves.Places.Ramification.CardFiberOverMulRamificationIndexMulInertiaDeg

/-!
# Complete splitting detected by the local symbol

The actual decomposition-group cardinality identifies complete splitting
with the vanishing of the whole local symbol.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The whole local Artin symbol is trivial exactly when both the actual
ramification index and residue degree are one. -/
theorem localArtin_trivial_iff_completelySplit (w : Place k L) :
    (∀ x : (w.restrict K).adicCompletionˣ, localArtin (K := K) w x = 1) ↔
      w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1 := by
  have htrivial : (∀ x : (w.restrict K).adicCompletionˣ,
      localArtin (K := K) w x = 1) ↔ localArtin (K := K) w = 1 :=
    ⟨fun h => MonoidHom.ext h, fun h x => DFunLike.congr_fun h x⟩
  rw [htrivial, ← MonoidHom.range_eq_bot_iff, localArtin_range, Subgroup.eq_bot_iff_card,
    IdeleGroup.decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg]
  constructor
  · intro h
    exact ⟨Nat.eq_one_of_dvd_one
      (h ▸ Nat.dvd_mul_right (w.ramificationIndex K) (w.inertiaDeg K)),
      Nat.eq_one_of_dvd_one
        (h ▸ Nat.dvd_mul_left (w.inertiaDeg K) (w.ramificationIndex K))⟩
  · rintro ⟨he, hf⟩
    rw [he, hf, mul_one]

/-- Complete splitting gives exactly as many places above the base place as
the global extension degree. -/
theorem card_fiberOver_eq_finrank_of_localArtin_trivial (w : Place k L)
    (h : ∀ x : (w.restrict K).adicCompletionˣ, localArtin (K := K) w x = 1) :
    ((w.restrict K).fiberOver L).card = Module.finrank K L := by
  obtain ⟨he, hf⟩ := (localArtin_trivial_iff_completelySplit (K := K) w).mp h
  have hdegree := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
    (w.restrict K) w rfl
  simpa only [he, hf, mul_one] using hdegree

end FunctionField
