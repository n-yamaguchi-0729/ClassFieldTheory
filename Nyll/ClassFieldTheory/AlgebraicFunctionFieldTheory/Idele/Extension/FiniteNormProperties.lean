/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor

/-!
# Continuity, degree, and towers for arbitrary finite class norms
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Every finite function-field norm is continuous in the ordinary quotient topology. -/
theorem continuous_finiteNorm :
    Continuous (finiteNorm (k := k) (K := K) (L := L)) := by
  apply continuous_coinduced_dom.2
  exact QuotientGroup.continuous_mk.comp
    (IdeleGroup.continuous_norm (k := k) (K := K) (L := L))

/-- The arbitrary finite class norm with its proved quotient continuity. -/
def finiteNormContinuous : IdeleClassGroup k L →ₜ* IdeleClassGroup k K where
  __ := finiteNorm (k := k) (K := K) (L := L)
  continuous_toFun := continuous_finiteNorm

/-- The quotient norm of every finite extension preserves the actual idele-class degree. -/
@[simp]
theorem degree_finiteNorm (c : IdeleClassGroup k L) :
    degree (k := k) (K := K) (finiteNorm (k := k) (K := K) (L := L) c) =
      degree (k := k) (K := L) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  change IdeleGroup.degree (k := k) (K := K) (IdeleGroup.norm (K := K) (L := L) a) =
    IdeleGroup.degree (k := k) (K := L) a
  exact IdeleGroup.degree_norm_of_finite a

variable {M : Type} [Field M] [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional L M] [AlgebraicCurve.HasPrincipalDivisors k M]

/-- Actual class norms compose along every finite tower, including inseparable parts. -/
theorem finiteNorm_trans (c : IdeleClassGroup k M) :
    let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
    finiteNorm (k := k) (K := K) (L := L)
        (finiteNorm (k := k) (K := L) (L := M) c) =
      finiteNorm (k := k) (K := K) (L := M) c := by
  intro hKMfinite
  refine QuotientGroup.induction_on c ?_
  intro a
  rw [finiteNorm_mk, finiteNorm_mk, finiteNorm_mk]
  exact congrArg (QuotientGroup.mk : IdeleGroup k K → IdeleClassGroup k K)
    (IdeleGroup.norm_trans (k := k) (K := K) (L := L) (M := M) a)

end FunctionField.IdeleClassGroup
