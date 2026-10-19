/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex

/-!
# Geometric pullback and reindexing of arithmetic constants

Changing the constant field inside the source function field does not change
the actual pullback divisor or class in a common geometric field.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k E Ω K L : Type*} [Field k] [Field E] [Field Ω] [Field K] [Field L]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    [Algebra k Ω] [Algebra E Ω] [Algebra Ω L]
    [Algebra k L] [Algebra E L]
    [IsScalarTower k Ω L] [IsScalarTower E Ω L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower E K L]
    [Algebra.IsIntegral k E] [Algebra.IsIntegral K L] [HasPrincipalDivisors Ω L]

/-- Actual divisor pullback commutes with changing the source constant field. -/
theorem pullbackConstants_divisorConstantEquiv (D : Divisor k K) :
    Divisor.pullbackConstants Ω L (divisorConstantEquiv k E K D) =
      Divisor.pullbackConstants Ω L D := by
  ext w
  rw [Divisor.pullbackConstants_apply, divisorConstantEquiv_apply,
    Divisor.pullbackConstants_apply]
  have hw : (Place.restrictConstants K (K := E) w).forgetConstants (K := k) =
      Place.restrictConstants K (K := k) w := Place.ext rfl
  rw [hw]
  rfl

/-- Actual Picard pullback commutes with changing the source constant field. -/
theorem baseChange_picConstantEquiv (x : Pic k K) :
    Pic.baseChange E Ω K L (picConstantEquiv k E K x) = Pic.baseChange k Ω K L x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  change H1Gm.mk (Divisor.pullbackConstants Ω L (divisorConstantEquiv k E K D)) =
    H1Gm.mk (Divisor.pullbackConstants Ω L D)
  rw [pullbackConstants_divisorConstantEquiv]

end FunctionField
