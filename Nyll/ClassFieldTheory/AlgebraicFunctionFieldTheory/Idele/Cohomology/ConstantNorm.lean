/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantNormKernel
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ClassHerbrand
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ClassNormObstruction

/-!
# Negative Tate vanishing and the Hasse norm theorem for actual constant extensions

Combine the actual norm index with the proved idele-class Herbrand quotient.
The negative-first group is trivial, so a principal idele that is an idele norm
already comes from a global field norm in the constructed constant extension.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- Negative-first Tate cohomology of the actual constant-extension idele class group vanishes. -/
theorem herbrandHMinusOne_subsingleton_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (σ : fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n)
    (hgen : ∀ τ : fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n,
      τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandHMinusOne
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n)
      (IdeleClassGroup k (fullConstantDegreeStage k K Ω n)) σ) := by
  obtain ⟨hC, hvalue⟩ := herbrandQuotient_eq_card (k := k) σ hgen
  have h0 : Finite (HerbrandH0
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n)
      (IdeleClassGroup k (fullConstantDegreeStage k K Ω n))) := hC.1
  have hm : Finite (HerbrandHMinusOne
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n)
      (IdeleClassGroup k (fullConstantDegreeStage k K Ω n)) σ) := hC.2
  rw [IsGalois.card_aut_eq_finrank, finrank_fullConstantDegreeStage] at hvalue
  apply herbrandHMinusOne_subsingleton_of_herbrandQuotient_eq_nat_of_le σ n
    (Nat.pos_of_ne_zero (NeZero.ne n)) hvalue
  rw [← Nat.card_congr
    (normQuotientEquivHerbrandH0 (k := k) (K := K)
      (L := fullConstantDegreeStage k K Ω n)).toEquiv,
    natCard_constantNormQuotient k K Ω n]

/-- For the actual constant extension, a principal idele norm is a global field norm. -/
theorem principalNormSubgroup_eq_fieldNormSubgroup_fullConstantDegreeStage
    (n : ℕ) [NeZero n] :
    NormObstruction.principalNormSubgroup (k := k) (K := K)
        (L := fullConstantDegreeStage k K Ω n) =
      NormObstruction.fieldNormSubgroup (K := K) (L := fullConstantDegreeStage k K Ω n) := by
  have hplace : Nonempty (Place k K) := FunctionField.nonempty_place k K
  have hcyclic : IsCyclic
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :=
    isCyclic_fullConstantDegreeStage k K Ω n
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator
    (α := fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n)
  have hvanish := herbrandHMinusOne_subsingleton_fullConstantDegreeStage k K Ω n σ hgen
  have hinj :=
    (NormObstruction.hasseNormDiagonal_injective_iff_class_herbrandHMinusOne_subsingleton
      (k := k) σ hgen).mpr hvanish
  exact le_antisymm (NormObstruction.hasseNormDiagonal_injective_iff.mp hinj)
    NormObstruction.fieldNormSubgroup_le_principalNormSubgroup

end FunctionField.IdeleClassGroup
