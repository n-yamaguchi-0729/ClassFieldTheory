/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.AlgebraicCurves.Places.Ramification.RamificationStabilizerOrder
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual completed Galois group

The actual global decomposition group has order `e * f`, equal to the degree
of the completed extension. Its faithful completed action therefore exhausts
the completed automorphism group. This proves that the completed extension is
Galois and identifies its whole Galois group with the actual decomposition group.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual global decomposition group has order equal to ramification times
residue degree. -/
theorem decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg (w : Place k L) :
    Nat.card (decompositionGroup (K := K) w) = w.ramificationIndex K * w.inertiaDeg K := by
  have hw : w.restrict L = w := by
    apply Place.ext
    exact SetLike.ext fun _ => Iff.rfl
  have h :=
    Place.ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer
      (F := K) (F' := L) (M := L) w
  change (w.restrict L).ramificationIndex K * (w.restrict L).inertiaDeg K *
    Nat.card (decompositionGroup (K := L) w) = Nat.card (decompositionGroup (K := K) w) at h
  rw [hw, Nat.card_unique, mul_one] at h
  exact h.symm

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual decomposition-group order equals the actual completed degree. -/
theorem decompositionGroup_card_eq_completion_finrank (w : Place k L) :
    Nat.card (decompositionGroup (K := K) w) =
      Module.finrank (w.restrict K).adicCompletion w.adicCompletion := by
  rw [decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg]
  exact_mod_cast (Place.finrank_adicCompletion_restrict (K := K) w).symm

/-- Every automorphism of the actual completed extension comes from the global
decomposition group. -/
theorem decompositionCompletionAut_bijective (w : Place k L) :
    Function.Bijective (decompositionCompletionAut (K := K) w) := by
  apply (decompositionCompletionAut_injective (K := K) w).bijective_of_nat_card_le
  rw [decompositionGroup_card_eq_completion_finrank, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- The completion of a finite Galois extension at an actual place is Galois
over its actual restricted-place completion. -/
instance completionIsGalois (w : Place k L) :
    IsGalois (w.restrict K).adicCompletion w.adicCompletion := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [← Nat.card_eq_of_bijective (decompositionCompletionAut (K := K) w)
    (decompositionCompletionAut_bijective (K := K) w)]
  exact decompositionGroup_card_eq_completion_finrank (K := K) w

/-- The actual decomposition group and completed Galois group are canonically
isomorphic via the completed action already used on idele components. -/
def decompositionCompletionEquiv (w : Place k L) :
    decompositionGroup (K := K) w ≃*
      (w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion) :=
  MulEquiv.ofBijective (decompositionCompletionAut (K := K) w)
    (decompositionCompletionAut_bijective (K := K) w)

/-- The completed Galois comparison agrees on the dense original field with
the original global automorphism. -/
@[simp]
theorem decompositionCompletionEquiv_algebraMap (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : L) :
    decompositionCompletionEquiv (K := K) w σ (algebraMap L w.adicCompletion x) =
      algebraMap L w.adicCompletion (σ.1 x) :=
  decompositionCompletionAut_algebraMap (K := K) w σ x

/-- A cyclic global extension has cyclic actual completed Galois groups. -/
instance completionGaloisGroupIsCyclic [IsCyclic (L ≃ₐ[K] L)] (w : Place k L) :
    IsCyclic (w.adicCompletion ≃ₐ[(w.restrict K).adicCompletion] w.adicCompletion) :=
  isCyclic_of_surjective (decompositionCompletionAut (K := K) w)
    (decompositionCompletionAut_bijective (K := K) w).surjective

end FunctionField.IdeleGroup
