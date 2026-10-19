/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Summing over a finite cyclic group

Enumerate an actual finite group by the powers of a proved generator.
-/

namespace CyclicAction

variable {G A : Type*} [Group G] [Fintype G] [AddCommMonoid A]

/-- A sum over a finite cyclic group is the sum over one full period of its generator. -/
theorem sum_eq_sum_range_generator (g : G) (hg : Subgroup.zpowers g = ⊤) (f : G → A) :
    ∑ x : G, f x = ∑ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  let e : Fin (orderOf g) ≃ G := (finEquivZPowers (isOfFinOrder_of_finite g)).trans
    ((MulEquiv.subgroupCongr hg).toEquiv.trans Subgroup.topEquiv.toEquiv)
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end CyclicAction
