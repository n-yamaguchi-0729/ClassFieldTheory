/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor

/-!
# Actual constant-extension norms are killed by the Frobenius character

The constant field adjoined in degree `n` embeds in the upper field, so every
upper divisor degree contains its constant-field degree. Norm preserves degree
over the initial finite base. Removing the degree of the full constants of the
original field therefore leaves a multiple of `n`.

This proves norm vanishing without assuming that the adjoined constants have
already been identified with the full constant field upstairs.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- Every actual norm class from the degree-`n` constant extension has normalized degree
divisible by `n`. The upper curve data come from its actual finite function-field stage. -/
theorem dvd_normalizedDegree_norm_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (c : IdeleClassGroup k (fullConstantDegreeStage k K Ω n)) :
    (n : ℤ) ∣ (normalizedDegree (k := k) (K := K)
      (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n) c)).toAdd := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := fullConstantDegreeStage k K Ω n) c
  change (n : ℤ) ∣ (degree (k := k) (K := K)
    (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)
      (mk (k := k) (K := fullConstantDegreeStage k K Ω n) a))).toAdd /
        (Module.finrank k (algebraicClosure k K) : ℤ)
  rw [degree_norm, degree_mk, IdeleGroup.degree_apply]
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let C := (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField
  let E := IntermediateField.adjoin K (C : Set Ω)
  let D : Divisor k E := (IdeleGroup.divisor (k := k)
    (K := fullConstantDegreeStage k K Ω n) a).toAdd
  have : IsScalarTower k (algebraicClosure k K) C :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k (algebraicClosure k K) Ω x)
  have : Finite C := Module.finite_of_finite (algebraicClosure k K)
  let _ : Algebra C E := constantAlgebra (K := K) C
  have : IsScalarTower k C E :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have hdim : Module.finrank k C = Module.finrank k (algebraicClosure k K) * n := by
    rw [← Module.finrank_mul_finrank k (algebraicClosure k K) C]
    exact congrArg (fun d => Module.finrank k (algebraicClosure k K) * d)
      (finrank_finiteConstantsInClosure (algebraicClosure k K) Ω n)
  have hdegree := degree_divisorConstantEquiv k C E D
  change (n : ℤ) ∣ Divisor.degree D / (Module.finrank k (algebraicClosure k K) : ℤ)
  refine ⟨Divisor.degree (divisorConstantEquiv k C E D), ?_⟩
  rw [hdegree, hdim, Nat.cast_mul, mul_assoc]
  exact Int.mul_ediv_cancel_left _
    (Int.natCast_ne_zero.mpr (fullConstants_degree_pos k K).ne')

/-- The actual constant-extension Frobenius character kills every actual idele-class norm. -/
theorem constantFrobeniusCharacter_norm (n : ℕ) [NeZero n]
    (c : IdeleClassGroup k (fullConstantDegreeStage k K Ω n)) :
    constantFrobeniusCharacter k K Ω n
      (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n) c) = 1 :=
  (constantFrobeniusCharacter_eq_one_iff k K Ω n _).mpr
    (dvd_normalizedDegree_norm_fullConstantDegreeStage k K Ω n c)

/-- The actual norm image lies in the kernel of the constant-extension Frobenius character. -/
theorem norm_range_le_ker_constantFrobeniusCharacter (n : ℕ) [NeZero n] :
    (norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range ≤
      (constantFrobeniusCharacter k K Ω n).ker := by
  rintro c ⟨b, rfl⟩
  exact constantFrobeniusCharacter_norm k K Ω n b

end FunctionField.IdeleClassGroup
