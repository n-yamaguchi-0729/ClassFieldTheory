/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Independence of the abelianized Galois group from a presentation

Two algebra isomorphisms between the same fields differ by an automorphism.
Their induced conjugations agree after abelianization.
-/

noncomputable section

namespace ClassFieldTheory

variable {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]

/-- The identification of abelianized Galois groups is independent of the algebra isomorphism. -/
theorem autCongr_abelianizationCongr_eq (e f : L ≃ₐ[K] E) :
    (AlgEquiv.autCongr e).abelianizationCongr = (AlgEquiv.autCongr f).abelianizationCongr := by
  apply MulEquiv.ext
  intro z
  refine QuotientGroup.induction_on z ?_
  intro σ
  change Abelianization.of (AlgEquiv.autCongr e σ) =
    Abelianization.of (AlgEquiv.autCongr f σ)
  let τ : E ≃ₐ[K] E := e.symm.trans f
  have hconj : AlgEquiv.autCongr f σ = τ * AlgEquiv.autCongr e σ * τ⁻¹ := by
    apply AlgEquiv.ext
    intro x
    simp only [τ, AlgEquiv.autCongr_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
      AlgEquiv.symm_apply_apply]
  rw [hconj, map_mul, map_mul, map_inv,
    mul_comm (Abelianization.of τ), mul_inv_cancel_right]

end ClassFieldTheory
