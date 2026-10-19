/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.ConstantTensorEquiv
import Nyll.ValuedFieldTheory.Valuation.Completion.BaseChangeNormTrace

/-!
# Norm comparison in a compositum with unchanged degree

The actual multiplication map identifies the compositum with the scalar extension
when its degree does not drop. The norm comparison follows from the determinant
under scalar extension.
-/

noncomputable section

open scoped TensorProduct

namespace FieldTheory

/-- Field norms commute with a scalar extension that preserves the extension degree. -/
theorem norm_algebraMap_of_generated_of_finrank_eq
    (k E K L : Type*) [Field k] [Field E] [Field K] [Field L]
    [Algebra k E] [Algebra k K] [Algebra k L]
    [Algebra E L] [Algebra K L] [IsScalarTower k E L] [IsScalarTower k K L]
    [FiniteDimensional k E] [FiniteDimensional K L]
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank K L = Module.finrank k E) (x : E) :
    Algebra.norm K (algebraMap E L x) = algebraMap k K (Algebra.norm k x) := by
  let e := constantTensorEquiv k E K L hgen hdeg
  have he : e (1 ⊗ₜ[k] x) = algebraMap E L x := by
    rw [constantTensorEquiv_tmul, map_one, one_mul]
  rw [← he, Algebra.norm_eq_of_algEquiv e]
  exact ValuationTheory.Completion.algebra_norm_baseChange_tmul x

end FieldTheory
