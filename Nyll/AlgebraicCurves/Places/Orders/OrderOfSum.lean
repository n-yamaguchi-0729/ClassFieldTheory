/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.RingTheory.Valuation.Basic

/-! # The order of a sum with distinct orders -/

@[expose] public section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- For the same place, two nonzero terms with distinct orders have sum order
equal to the minimum of their orders. -/
theorem ord_add_eq_min_of_ne {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f ≠ v.ord g) : v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon; exact h (by simp only [Place.ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, map_zero] at h1
    rcases max_choice (v.adicValuation f) (v.adicValuation g) with hm | hm
    · exact (v.adicValuation_ne_zero hf) (h1 ▸ hm).symm
    · exact (v.adicValuation_ne_zero hg) (h1 ▸ hm).symm
  simp only [Place.ord, h1]
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    rw [hmax]; omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    rw [hmax]; omega

end AlgebraicCurve.Place
