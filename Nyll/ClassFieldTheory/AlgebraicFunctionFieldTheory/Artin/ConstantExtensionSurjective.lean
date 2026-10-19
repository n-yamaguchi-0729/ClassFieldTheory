/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegreeSurjective
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Surjectivity of the actual constant-extension Frobenius character

An idele class of each normalized degree realizes each power of arithmetic
Frobenius. Since that actual Frobenius has the full Galois-group order, the
character is surjective and its kernel quotient has exactly the extension degree.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable (k K : Type) (Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra K Ω] [IsSepClosed Ω]

/-- Every automorphism of the actual constant extension is realized by an idele class. -/
theorem constantFrobeniusCharacter_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (constantFrobeniusCharacter k K Ω n) := by
  have htop : Subgroup.zpowers (fullConstantDegreeFrobenius k K Ω n) = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top
      (Subgroup.zpowers (fullConstantDegreeFrobenius k K Ω n))).mp
    rw [Nat.card_zpowers, orderOf_fullConstantDegreeFrobenius,
      IsGalois.card_aut_eq_finrank, finrank_fullConstantDegreeStage]
  intro σ
  have hσ : σ ∈ Subgroup.zpowers (fullConstantDegreeFrobenius k K Ω n) :=
    htop ▸ Subgroup.mem_top σ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨c, hc⟩ := normalizedDegree_surjective (k := k) (K := K) (Multiplicative.ofAdd i)
  refine ⟨c, ?_⟩
  rw [constantFrobeniusCharacter_apply, hc, toAdd_ofAdd]
  exact hi

/-- The quotient by the actual Frobenius-character kernel is the actual Galois group. -/
def constantFrobeniusCharacterQuotientEquiv (n : ℕ) [NeZero n] :
    IdeleClassGroup k K ⧸ (constantFrobeniusCharacter k K Ω n).ker ≃*
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :=
  QuotientGroup.quotientKerEquivOfSurjective (constantFrobeniusCharacter k K Ω n)
    (constantFrobeniusCharacter_surjective k K Ω n)

/-- The kernel quotient has exactly the constant-extension degree. -/
theorem natCard_constantFrobeniusCharacter_quotient (n : ℕ) [NeZero n] :
    Nat.card (IdeleClassGroup k K ⧸ (constantFrobeniusCharacter k K Ω n).ker) = n := by
  rw [Nat.card_congr (constantFrobeniusCharacterQuotientEquiv k K Ω n).toEquiv,
    IsGalois.card_aut_eq_finrank, finrank_fullConstantDegreeStage]

end FunctionField.IdeleClassGroup
