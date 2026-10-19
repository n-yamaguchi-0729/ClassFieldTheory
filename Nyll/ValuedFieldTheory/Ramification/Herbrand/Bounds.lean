/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.Herbrand.Function

/-!
# Upper bounds for the Herbrand function

Every slope is at most one, since each lower group embeds into inertia.
At integral levels this bounds the upper numbering by the lower numbering.
-/

namespace RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration

variable {G : Type*} [Group G] [Finite G]

/-- The normalized Herbrand slopes never exceed one. -/
theorem herbrandSlope_le_one (F : AntitoneNormalSubgroupFiltration G) (n : ℕ) :
    herbrandSlope F n ≤ 1 := by
  have hsub : F.lower (n + 1) ≤ F.lower 0 := F.antitone (Nat.zero_le _)
  let incl : F.lower (n + 1) → F.lower 0 := fun x => ⟨x.val, hsub x.property⟩
  have hinj : Function.Injective incl := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : F.lower 0 => (z : G)) h)
  have hcard : Nat.card (F.lower (n + 1)) ≤ Nat.card (F.lower 0) :=
    Nat.card_le_card_of_injective incl hinj
  have hden : (0 : ℝ) < Nat.card (F.lower 0) :=
    Nat.cast_pos.mpr Finite.card_pos
  exact (div_le_one hden).mpr (Nat.cast_le.mpr hcard)

/-- The Herbrand value at an integral level is bounded by that level. -/
theorem herbrandFunction_nat_le (F : AntitoneNormalSubgroupFiltration G) (n : ℕ) :
    herbrandFunction F (n : ℝ) ≤ n := by
  rw [herbrandFunction_nat, herbrandValueNat]
  calc
    ∑ i ∈ Finset.range n, herbrandSlope F i ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => herbrandSlope_le_one F i
    _ = n := by rw [Finset.sum_const, Finset.card_range, nsmul_one]

end RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
