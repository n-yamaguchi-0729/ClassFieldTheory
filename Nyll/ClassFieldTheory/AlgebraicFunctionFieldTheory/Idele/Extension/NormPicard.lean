/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor

/-!
# Compatibility of actual idele and Picard norms

Passing from an idele class to its divisor class commutes with the norm.
Both norms are computed from the existing inertia-weighted divisor pushforward.
-/

noncomputable section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

namespace IdeleGroup

/-- The divisor class of an actual idele norm is the actual norm of its divisor class. -/
theorem divisorClass_norm (a : IdeleGroup k L) :
    divisorClass (k := k) (K := K) (norm (K := K) (L := L) a) =
      (AlgebraicCurve.Pic.norm (k := k) (K := K) (L := L)).toMultiplicative
        (divisorClass (k := k) (K := L) a) := by
  apply Multiplicative.ext
  change AlgebraicCurve.H1Gm.mk (divisor (k := k) (K := K)
    (norm (K := K) (L := L) a)).toAdd =
      AlgebraicCurve.H1Gm.mk (AlgebraicCurve.Divisor.pushforward K
        (divisor (k := k) (K := L) a).toAdd)
  rw [divisor_norm]

end IdeleGroup

namespace IdeleClassGroup

/-- The actual norm commutes with passage from idele classes to full Picard classes. -/
theorem divisorClass_norm (c : IdeleClassGroup k L) :
    divisorClass (k := k) (K := K) (norm (K := K) (L := L) c) =
      (AlgebraicCurve.Pic.norm (k := k) (K := K) (L := L)).toMultiplicative
        (divisorClass (k := k) (K := L) c) := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  exact IdeleGroup.divisorClass_norm a

end IdeleClassGroup

end FunctionField
