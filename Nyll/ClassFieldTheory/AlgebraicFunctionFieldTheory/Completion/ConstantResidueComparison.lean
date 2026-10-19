/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFrobeniusResidue
import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion

/-!
# Completing the residue action of constant Frobenius

The original residue field and the residue field of the completion are
identified by their existing canonical isomorphism. This isomorphism
intertwines the original and completed actions of the decomposition group.
In particular, completing the actual constant Frobenius preserves its
arithmetic power action on the residue field.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The completed decomposition action restricted to the actual integral subring. -/
def decompositionCompletionIntegerEquiv (w : Place k L)
    (σ : decompositionGroup (K := K) w) :
    w.adicCompletionIntegers ≃+* w.adicCompletionIntegers :=
  (decompositionCompletionAut (K := K) w σ).toRingEquiv.restrict
    w.adicCompletionIntegers w.adicCompletionIntegers
    (fun x => (decompositionCompletionAut_mem_integers_iff w σ x).symm)

/-- Completion of the original valuation-ring action agrees with the restriction
of the completed field action. -/
theorem decompositionCompletionIntegerEquiv_algebraMap (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.toValuationSubring) :
    decompositionCompletionIntegerEquiv w σ
        (algebraMap w.toValuationSubring w.adicCompletionIntegers x) =
      algebraMap w.toValuationSubring w.adicCompletionIntegers
        (decompositionValuationEquiv w σ x) := by
  apply Subtype.ext
  change decompositionCompletionAut (K := K) w σ
      (algebraMap L w.adicCompletion (x : L)) =
    algebraMap L w.adicCompletion (decompositionValuationEquiv w σ x : L)
  rw [decompositionCompletionAut_algebraMap, decompositionValuationEquiv_coe]

/-- The canonical residue comparison intertwines the decomposition actions
before and after completion. -/
theorem decompositionCompletion_residue_comparison (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.ResidueField) :
    IsLocalRing.ResidueField.mapEquiv (decompositionCompletionIntegerEquiv w σ)
        (IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
          L w.heightOneSpectrum x) =
      IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
        L w.heightOneSpectrum (decompositionResidueRingAut (K := K) w σ x) := by
  let e : w.ResidueField ≃+* IsLocalRing.ResidueField w.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      L w.heightOneSpectrum
  have he (a : w.toValuationSubring) :
      e (IsLocalRing.residue w.toValuationSubring a) =
        IsLocalRing.residue w.adicCompletionIntegers
          (algebraMap w.toValuationSubring w.adicCompletionIntegers a) := rfl
  change IsLocalRing.ResidueField.mapEquiv (decompositionCompletionIntegerEquiv w σ)
    (e x) = e (decompositionResidueRingAut (K := K) w σ x)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  calc
    _ = IsLocalRing.residue w.adicCompletionIntegers
        (decompositionCompletionIntegerEquiv w σ
          (algebraMap w.toValuationSubring w.adicCompletionIntegers a)) := by
      rw [he, IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    _ = IsLocalRing.residue w.adicCompletionIntegers
        (algebraMap w.toValuationSubring w.adicCompletionIntegers
          (decompositionValuationEquiv w σ a)) :=
      congrArg (IsLocalRing.residue w.adicCompletionIntegers)
        (decompositionCompletionIntegerEquiv_algebraMap w σ a)
    _ = _ := by
      rw [decompositionResidueRingAut_residue]
      exact (he (decompositionValuationEquiv w σ a)).symm

end FunctionField.IdeleGroup

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]

/-- On the completed residue field, the actual constant decomposition Frobenius
acts by the cardinality power of the completed base residue field. -/
theorem fullConstantDegreeFrobeniusDecomposition_completion_residue
    (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n))
    (x : IsLocalRing.ResidueField w.adicCompletionIntegers) :
    IsLocalRing.ResidueField.mapEquiv
        (IdeleGroup.decompositionCompletionIntegerEquiv w
          (fullConstantDegreeFrobeniusDecomposition k K Ω n w)) x =
      x ^ Nat.card (IsLocalRing.ResidueField (w.restrict K).adicCompletionIntegers) := by
  let e : w.ResidueField ≃+* IsLocalRing.ResidueField w.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      (fullConstantDegreeStage k K Ω n) w.heightOneSpectrum
  let ebase : (w.restrict K).ResidueField ≃+*
      IsLocalRing.ResidueField (w.restrict K).adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      K (w.restrict K).heightOneSpectrum
  obtain ⟨y, rfl⟩ := e.surjective x
  calc
    _ = e (IdeleGroup.decompositionResidueAut (K := K) w
        (fullConstantDegreeFrobeniusDecomposition k K Ω n w) y) :=
      IdeleGroup.decompositionCompletion_residue_comparison w
        (fullConstantDegreeFrobeniusDecomposition k K Ω n w) y
    _ = e (y ^ Nat.card (w.restrict K).ResidueField) :=
      congrArg e (fullConstantDegreeFrobeniusDecomposition_residue k K Ω n w y)
    _ = e y ^ Nat.card (w.restrict K).ResidueField := map_pow e y _
    _ = _ := congrArg (fun m : ℕ => e y ^ m) (Nat.card_congr ebase.toEquiv)

end FunctionField
