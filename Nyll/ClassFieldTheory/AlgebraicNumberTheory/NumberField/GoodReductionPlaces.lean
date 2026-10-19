/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DegreeOnePrimes

/-!
# Finite-place avoidance for arithmetic models

The existing degree-one-prime theorem avoids finite sets of places by
excluding the absolute norms of their contractions to the rational integers.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace AlgebraicNumberTheory.PrimeSelection

/-- An unramified degree-one place can avoid both prescribed finite places
and prescribed rational residue characteristics. -/
theorem exists_unramified_degreeOnePrime_avoiding
    (K : Type*) [Field K] [NumberField K]
    (bad : Finset ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ q : ℕ, q.Prime ∧ q ∉ bad ∧
      ∃ W : HeightOneSpectrum (𝓞 K), W ∉ S ∧
        W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) ∧
        W.asIdeal.inertiaDeg ℤ = 1 ∧ Algebra.IsUnramifiedAt ℤ W.asIdeal := by
  classical
  let norms := S.image (fun W => Ideal.absNorm (W.asIdeal.under ℤ))
  obtain ⟨q, hq, hbad, W, hOver, hdeg, hur⟩ :=
    exists_unramified_degreeOnePrime_not_mem K (bad ∪ norms)
  have : Fact q.Prime := ⟨hq⟩
  have : W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hOver
  have hnorm : Ideal.absNorm (W.asIdeal.under ℤ) = q := by
    rw [← Ideal.over_def W.asIdeal (Ideal.span ({(q : ℤ)} : Set ℤ)),
      Ideal.absNorm_span_natCast, Module.finrank_self, pow_one]
  refine ⟨q, hq, fun h => hbad (Finset.mem_union_left _ h), W, ?_, hOver, hdeg, hur⟩
  intro hW
  apply hbad
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨W, hW, hnorm⟩

end AlgebraicNumberTheory.PrimeSelection
