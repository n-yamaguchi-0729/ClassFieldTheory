/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# The common descent of the actual function-field idele norm

The separable and arbitrary finite arithmetic proofs establish preservation
of principal ideles in different generalities. Both supply that proposition
to this single quotient construction; no new norm or class-group carrier is chosen.
-/

@[expose] public section

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Descend the original idele norm using its proved preservation of principal ideles. -/
noncomputable def normOfPrincipal
    (hprincipal : IdeleGroup.principalSubgroup k L ≤
      (IdeleGroup.principalSubgroup k K).comap (IdeleGroup.norm (K := K) (L := L))) :
    IdeleClassGroup k L →* IdeleClassGroup k K :=
  QuotientGroup.map (IdeleGroup.principalSubgroup k L) (IdeleGroup.principalSubgroup k K)
    (IdeleGroup.norm (K := K) (L := L)) hprincipal

/-- The common quotient norm is the actual idele norm on every representative. -/
@[simp]
theorem normOfPrincipal_mk
    (hprincipal : IdeleGroup.principalSubgroup k L ≤
      (IdeleGroup.principalSubgroup k K).comap (IdeleGroup.norm (K := K) (L := L)))
    (a : IdeleGroup k L) :
    normOfPrincipal hprincipal (QuotientGroup.mk a) =
      QuotientGroup.mk (IdeleGroup.norm (K := K) (L := L) a) := rfl

end FunctionField.IdeleClassGroup
