/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Normal.Basic

/-!
# Equality of normal field realizations

All embeddings of a normal extension into the same ambient field have the
same field range. This separates independence of the embedded subfield
from independence of its chosen parameterization.
-/

noncomputable section

namespace ClassFieldTheory

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Normal K L]

/-- Two embeddings of a normal extension have the same intermediate-field image. -/
theorem fieldRange_eq_of_normal (i j : L →ₐ[K] Ω) : i.fieldRange = j.fieldRange := by
  let e : L ≃ₐ[K] i.fieldRange := AlgEquiv.ofInjectiveField i
  have hnormal : Normal K i.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (j.comp e.symm.toAlgHom)
  rw [← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map] at h
  exact h.symm

end ClassFieldTheory
