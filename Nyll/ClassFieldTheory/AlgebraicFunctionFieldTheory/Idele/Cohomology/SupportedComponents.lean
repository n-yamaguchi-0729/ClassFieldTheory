/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeles

/-! # Actual ideles supported on a finite set of places -/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Every tuple of completed units on a finite set extends to an actual
S-idele equal to one outside that set. -/
theorem exists_supported_sIdele (S : Finset (Place k K))
    (x : ∀ v : S, v.val.adicCompletionˣ) :
    ∃ a : sIdeles S, (∀ v : S, a.val v.val = x v) ∧
      ∀ v : Place k K, v ∉ S → a.val v = 1 := by
  classical
  let b : IdeleGroup k K := ⟨fun v => if h : v ∈ S then x ⟨v, h⟩ else 1, by
    have hnot : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ S :=
      S.finite_toSet.compl_mem_cofinite
    exact hnot.mono fun v hv => by
      simp only [dite_eq_right hv]
      exact v.adicCompletionIntegers.units.one_mem⟩
  have hbout (v : Place k K) (hv : v ∉ S) : b v = 1 := dite_eq_right hv
  have hb : b ∈ sIdeles S := by
    intro v hv
    rw [hbout v hv]
    exact v.adicCompletionIntegers.units.one_mem
  refine ⟨⟨b, hb⟩, ?_, hbout⟩
  intro v
  exact dite_eq_left v.property

end FunctionField.IdeleGroup
