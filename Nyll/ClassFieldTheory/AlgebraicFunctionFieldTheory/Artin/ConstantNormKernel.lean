/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantPicardNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtensionPicard
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtensionSurjective

/-!
# Actual constant-extension norm kernel and reciprocity quotient

The actual Picard norm criterion and the unramified idele lifting theorem
identify the actual norm subgroup with the kernel of the Frobenius character.
Its quotient is the actual Galois group and has exactly the extension degree.
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

/-- An actual class is a constant-extension norm exactly when its normalized degree is divisible. -/
theorem mem_norm_range_fullConstantDegreeStage_iff (n : ℕ) [NeZero n]
    (c : IdeleClassGroup k K) :
    c ∈ (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range ↔
      (n : ℤ) ∣ (normalizedDegree (k := k) (K := K) c).toAdd := by
  rw [mem_norm_range_fullConstantDegreeStage_iff_picard]
  have hdeg : H1Gm.degree k K (divisorClass (k := k) (K := K) c).toAdd =
      (degree (k := k) (K := K) c).toAdd := by
    obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
    rfl
  change _ ↔ (n : ℤ) ∣ (degree (k := k) (K := K) c).toAdd /
    (Module.finrank k (algebraicClosure k K) : ℤ)
  rw [← hdeg]
  exact mem_picardNorm_fullConstantDegreeStage_iff k K Ω n
    (divisorClass (k := k) (K := K) c).toAdd

/-- The actual constant-extension norm subgroup is exactly the Frobenius-character kernel. -/
theorem norm_range_eq_ker_constantFrobeniusCharacter (n : ℕ) [NeZero n] :
    (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range =
      (constantFrobeniusCharacter k K Ω n).ker := by
  ext c
  exact (mem_norm_range_fullConstantDegreeStage_iff k K Ω n c).trans
    (constantFrobeniusCharacter_eq_one_iff k K Ω n c).symm

/-- Reciprocity identifies the actual constant-extension norm quotient with its Galois group. -/
def constantNormQuotientEquiv (n : ℕ) [NeZero n] :
    (IdeleClassGroup k K ⧸
      (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range) ≃*
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (norm_range_eq_ker_constantFrobeniusCharacter k K Ω n)).trans
      (constantFrobeniusCharacterQuotientEquiv k K Ω n)

/-- The actual constant-extension idele-class norm index is its degree. -/
theorem natCard_constantNormQuotient (n : ℕ) [NeZero n] :
    Nat.card (IdeleClassGroup k K ⧸
      (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range) = n := by
  rw [Nat.card_congr (constantNormQuotientEquiv k K Ω n).toEquiv,
    IsGalois.card_aut_eq_finrank, finrank_fullConstantDegreeStage]

end FunctionField.IdeleClassGroup
