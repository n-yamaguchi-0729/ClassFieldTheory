/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindexNorm
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PicardNormConstants

/-! # Actual constant reindexing in towers and compatibility with norms -/

@[expose] public section

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k C E L : Type*} [Field k] [Field C] [Field E] [Field L]
  [Algebra k C] [Algebra k E] [Algebra C E] [IsScalarTower k C E]
  [Algebra k L] [Algebra C L] [Algebra E L]
  [IsScalarTower k C L] [IsScalarTower k E L] [IsScalarTower C E L]
  [Algebra.IsIntegral k C] [Algebra.IsIntegral k E] [Algebra.IsIntegral C E]

omit [IsScalarTower k C E] in
/-- Reindexing twice retains the same underlying valuation ring. -/
theorem divisorConstantEquiv_trans (D : Divisor k L) :
    divisorConstantEquiv C E L (divisorConstantEquiv k C L D) =
      divisorConstantEquiv k E L D := by
  ext v
  rw [divisorConstantEquiv_apply, divisorConstantEquiv_apply, divisorConstantEquiv_apply]
  have hv : (v.forgetConstants (K := C)).forgetConstants (K := k) =
      v.forgetConstants (K := k) := Place.ext rfl
  rw [hv]

omit [IsScalarTower k C E] in
/-- The actual Picard equivalences compose in a constant tower. -/
theorem picConstantEquiv_trans (x : Pic k L) :
    picConstantEquiv C E L (picConstantEquiv k C L x) =
      picConstantEquiv k E L x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [picConstantEquiv_mk, picConstantEquiv_mk, picConstantEquiv_mk,
    divisorConstantEquiv_trans]

variable {K : Type*} [Field K] [Algebra k K] [Algebra C K] [IsScalarTower k C K]
  [Algebra K L] [IsScalarTower k K L] [IsScalarTower C K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [HasPrincipalDivisors k L] [HasPrincipalDivisors C L]

omit [IsScalarTower k C E] in
/-- Computing over the initial constants and then reindexing is the
actual Picard norm between the two larger constant fields. -/
theorem picConstantEquiv_normConstants (x : Pic E L) :
    picConstantEquiv k C K
        (Pic.norm (K := K) ((picConstantEquiv k E L).symm x)) =
      Pic.normConstants C E K L x := by
  rw [picConstantEquiv_norm]
  change Pic.norm (K := K)
    (picConstantEquiv k C L ((picConstantEquiv k E L).symm x)) =
      Pic.norm (K := K) ((picConstantEquiv C E L).symm x)
  apply congrArg (Pic.norm (k := C) (K := K) (L := L))
  apply (picConstantEquiv C E L).injective
  rw [picConstantEquiv_trans, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end FunctionField
