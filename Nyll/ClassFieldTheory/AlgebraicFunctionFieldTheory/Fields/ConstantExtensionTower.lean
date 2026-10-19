/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFieldExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure

/-!
# Constant-field extensions of every positive degree

Inside a separably closed overfield of a function field, adjoining the degree-`n`
extension of its actual full constants produces a finite Galois extension of
degree exactly `n`. Its Frobenius is an actual automorphism fixing the original
function field and has order `n`. The original finite base need not be full.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- The actual degree-`n` constant extension of `K` inside the chosen separably
closed overfield, viewed as a finite Galois intermediate field. -/
def fullConstantDegreeStage (n : ℕ) [NeZero n] : FiniteGaloisIntermediateField K Ω :=
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  constantExtensionStage (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- Constant extensions of every positive degree have that exact degree over
the original function field. -/
theorem finrank_fullConstantDegreeStage (n : ℕ) [NeZero n] :
    Module.finrank K (fullConstantDegreeStage k K Ω n) = n := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  change Module.finrank K (IntermediateField.adjoin K
    ((finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField : Set Ω)) = n
  rw [finrank_constantExtension _ (separableConstants_fullConstants k K)]
  exact finrank_finiteConstantsInClosure (algebraicClosure k K) Ω n

/-- Arithmetic Frobenius of the actual degree-`n` constant extension. -/
def fullConstantDegreeFrobenius (n : ℕ) [NeZero n] :
    fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n :=
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  fullConstantExtensionFrobenius (k := k) (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- The arithmetic Frobenius of the degree-`n` constant extension has order `n`. -/
theorem orderOf_fullConstantDegreeFrobenius (n : ℕ) [NeZero n] :
    orderOf (fullConstantDegreeFrobenius k K Ω n) = n := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact (orderOf_fullConstantExtensionFrobenius (k := k) (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField).trans
      (finrank_fullConstantDegreeStage k K Ω n)

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- These actual constant-field Galois groups are cyclic. -/
theorem isCyclic_fullConstantDegreeStage (n : ℕ) [NeZero n] :
    IsCyclic (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact isCyclic_constantExtension (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField

end FunctionField
