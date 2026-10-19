/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex

/-!
# Picard norms with different constant fields

Reindex the source places over the smaller constants and apply actual divisor
pushforward. This is the same norm image, with arithmetic degrees scaled by
the source constant-field degree.
-/

noncomputable section

namespace AlgebraicCurve.Pic

variable (k E K L : Type*) [Field k] [Field E] [Field K] [Field L]
    [Algebra k E] [Algebra k K] [Algebra k L] [Algebra E L]
    [IsScalarTower k E L] [Algebra.IsIntegral k E]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [HasPrincipalDivisors k L]

/-- The actual Picard norm from the larger full constant field to the smaller one. -/
def normConstants : Pic E L →+ Pic k K :=
  (norm (k := k) (K := K) (L := L)).comp
    (FunctionField.picConstantEquiv k E L).symm.toAddMonoidHom

/-- Reindexing the source does not change the actual norm image. -/
theorem range_normConstants :
    (normConstants k E K L).range = (norm (k := k) (K := K) (L := L)).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(FunctionField.picConstantEquiv k E L).symm y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨FunctionField.picConstantEquiv k E L y, ?_⟩
    change norm ((FunctionField.picConstantEquiv k E L).symm
      (FunctionField.picConstantEquiv k E L y)) = _
    rw [AddEquiv.symm_apply_apply]

/-- The norm scales degrees measured over the respective constant fields. -/
theorem degree_normConstants [HasPrincipalDivisors k K] [HasPrincipalDivisors E L]
    (x : Pic E L) :
    H1Gm.degree k K (normConstants k E K L x) =
      (Module.finrank k E : ℤ) * H1Gm.degree E L x := by
  change H1Gm.degree k K (norm ((FunctionField.picConstantEquiv k E L).symm x)) = _
  rw [degree_norm, FunctionField.degree_picConstantEquiv k E L, AddEquiv.apply_symm_apply]

end AlgebraicCurve.Pic
