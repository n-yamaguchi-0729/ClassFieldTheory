/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Normalized degree under degree-one field inclusions

An isomorphism of the fields identifies their algebraic constant fields.
Together with the actual degree formula for base change, this preserves the
normalized idele-class degree.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- A degree-one field inclusion preserves the actual normalized idele-class degree. -/
theorem normalizedDegree_baseChange_of_finrank_one (h : Module.finrank K L = 1)
    (c : IdeleClassGroup k K) :
    normalizedDegree (k := k) (K := L) (baseChange (k := k) (K := K) (L := L) c) =
      normalizedDegree (k := k) (K := K) c := by
  let e : K ≃ₐ[k] L := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K L)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)
  have hc : Module.finrank k (algebraicClosure k K) =
      Module.finrank k (algebraicClosure k L) := e.algebraicClosure.toLinearEquiv.finrank_eq
  apply Multiplicative.ext
  change (degree (k := k) (K := L) (baseChange (k := k) (K := K) (L := L) c)).toAdd /
      Module.finrank k (algebraicClosure k L) =
    (degree (k := k) (K := K) c).toAdd / Module.finrank k (algebraicClosure k K)
  rw [degree_baseChange, h, Nat.cast_one, one_mul, hc]

end FunctionField.IdeleClassGroup
