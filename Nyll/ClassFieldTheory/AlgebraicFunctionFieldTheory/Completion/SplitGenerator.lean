/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm

/-!
# A generating element in the base completion

The actual decomposition group is trivial when a field generator already
lies in the base completion. The resulting degree-one norm is surjective.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A generator contained in the base completion makes the completed degree one. -/
theorem completion_finrank_eq_one_of_generator
    (w : Place k L) (β : L) (hgen : Algebra.adjoin K {β} = ⊤)
    (c : (w.restrict K).adicCompletion)
    (hc : algebraMap (w.restrict K).adicCompletion w.adicCompletion c =
      algebraMap L w.adicCompletion β) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion = 1 := by
  have htrivial (σ : decompositionGroup (K := K) w) : σ = 1 := by
    apply Subtype.ext
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro z hz
    have hzβ : z = β := Set.mem_singleton_iff.mp hz
    subst z
    simp only [AlgEquiv.coe_toAlgHom, Subgroup.coe_one, AlgEquiv.one_apply]
    apply (algebraMap L w.adicCompletion).injective
    rw [← decompositionCompletionAut_algebraMap w σ, ← hc,
      (decompositionCompletionAut (K := K) w σ).commutes]
  have hsub : Subsingleton (decompositionGroup (K := K) w) :=
    ⟨fun σ τ => (htrivial σ).trans (htrivial τ).symm⟩
  rw [← decompositionGroup_card_eq_completion_finrank]
  exact Nat.card_unique

/-- The norm of a degree-one completion is onto, with preimages from the base. -/
theorem localNorm_surjective_of_completion_finrank_eq_one (w : Place k L)
    (hdegree : Module.finrank (w.restrict K).adicCompletion w.adicCompletion = 1) :
    Function.Surjective (localNorm (K := K) w) := by
  intro y
  refine ⟨Units.map (algebraMap (w.restrict K).adicCompletion w.adicCompletion) y, ?_⟩
  apply Units.ext
  change Algebra.norm (w.restrict K).adicCompletion
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion
      (y : (w.restrict K).adicCompletion)) = (y : (w.restrict K).adicCompletion)
  rw [Algebra.norm_algebraMap, hdegree, pow_one]

end FunctionField.IdeleGroup
