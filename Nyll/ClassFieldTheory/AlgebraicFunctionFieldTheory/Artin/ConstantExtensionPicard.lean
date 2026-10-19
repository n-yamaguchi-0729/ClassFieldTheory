/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.UnramifiedNormPicard

/-!
# Actual constant-extension norms are detected by Picard norms

The constructed finite constant extension is everywhere unramified. Its actual
idele-class norm quotient therefore identifies with its actual Picard norm
quotient, without any unramifiedness or norm-lifting hypothesis from the caller.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- Actual constant-extension norm membership is detected on the actual divisor class. -/
theorem mem_norm_range_fullConstantDegreeStage_iff_picard (n : ℕ) [NeZero n]
    (c : IdeleClassGroup k K) :
    c ∈ (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range ↔
      divisorClass (k := k) (K := K) c ∈
        (Pic.norm (k := k) (K := K)
          (L := fullConstantDegreeStage k K Ω n)).toMultiplicative.range :=
  mem_norm_range_iff_picard_of_unramified
    (ramificationIndex_fullConstantDegreeStage k K Ω n) c

/-- The actual degree-n constant-extension norm quotient is its actual Picard norm quotient. -/
def normQuotientEquivPicard_fullConstantDegreeStage (n : ℕ) [NeZero n] :
    (IdeleClassGroup k K ⧸
      (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range) ≃*
      (Multiplicative (Pic k K) ⧸
        (Pic.norm (k := k) (K := K)
          (L := fullConstantDegreeStage k K Ω n)).toMultiplicative.range) :=
  normQuotientEquivPicard_of_unramified (ramificationIndex_fullConstantDegreeStage k K Ω n)

end FunctionField.IdeleClassGroup
