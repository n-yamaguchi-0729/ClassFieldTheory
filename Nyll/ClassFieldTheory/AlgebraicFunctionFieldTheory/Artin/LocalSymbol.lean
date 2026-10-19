/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalValuationNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue

/-!
# Local Artin symbols in the actual global decomposition group

Local reciprocity on the existing place completions is transported through
the completed decomposition-group equivalence. Its image is exactly the
decomposition group and its kernel is the actual completed norm image.
The existing local reciprocity valuation is the negative of the divisor
order, so inversion on the input gives the arithmetic divisor convention.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Local reciprocity with values in the actual global decomposition group. -/
def localDecompositionArtin (w : Place k L) :
    (w.restrict K).adicCompletionˣ →ₜ* IdeleGroup.decompositionGroup (K := K) w := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  exact
    { toMonoidHom := (IdeleGroup.decompositionCompletionEquiv (K := K) w).symm.toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMap
          (w.restrict K).adicCompletion w.adicCompletion).toMonoidHom.comp
            (invMonoidHom : (w.restrict K).adicCompletionˣ →*
              (w.restrict K).adicCompletionˣ))
      continuous_toFun := (continuous_of_discreteTopology :
        Continuous (IdeleGroup.decompositionCompletionEquiv (K := K) w).symm).comp
        (LocalClassFieldTheory.abelianLocalArtinMap
          (w.restrict K).adicCompletion w.adicCompletion).continuous |>.comp continuous_inv }

/-- The completed decomposition automorphism is the existing local Artin
value with the arithmetic input convention. -/
theorem localDecompositionArtin_completion (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    IdeleGroup.decompositionCompletionEquiv (K := K) w
        (localDecompositionArtin (K := K) w x) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (w.restrict K).adicCompletion w.adicCompletion x⁻¹ := by
  intro hrelation hlocal
  change IdeleGroup.decompositionCompletionEquiv (K := K) w
    ((IdeleGroup.decompositionCompletionEquiv (K := K) w).symm
      (LocalClassFieldTheory.abelianLocalArtinMap
        (w.restrict K).adicCompletion w.adicCompletion x⁻¹)) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom
      (w.restrict K).adicCompletion w.adicCompletion) x⁻¹

/-- Every actual decomposition automorphism is a local Artin value. -/
theorem localDecompositionArtin_surjective (w : Place k L) :
    Function.Surjective (localDecompositionArtin (K := K) w) := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  intro σ
  obtain ⟨x, hx⟩ := LocalClassFieldTheory.abelianLocalArtinMap_surjective
    (w.restrict K).adicCompletion w.adicCompletion
    (IdeleGroup.decompositionCompletionEquiv (K := K) w σ)
  refine ⟨x⁻¹, ?_⟩
  change (IdeleGroup.decompositionCompletionEquiv (K := K) w).symm
    (LocalClassFieldTheory.abelianLocalArtinMap
      (w.restrict K).adicCompletion w.adicCompletion (x⁻¹)⁻¹) = σ
  rw [inv_inv, hx, MulEquiv.symm_apply_apply]

/-- The local Artin kernel is the genuine completed field-norm image. -/
theorem localDecompositionArtin_ker (w : Place k L) :
    (localDecompositionArtin (K := K) w).toMonoidHom.ker =
      (IdeleGroup.localNorm (K := K) w).range := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  ext x
  change (IdeleGroup.decompositionCompletionEquiv (K := K) w).symm
      (LocalClassFieldTheory.abelianLocalArtinMap
        (w.restrict K).adicCompletion w.adicCompletion x⁻¹) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, map_inv, inv_eq_one]
  change x ∈ (LocalClassFieldTheory.abelianLocalArtinMap
      (w.restrict K).adicCompletion w.adicCompletion).toMonoidHom.ker ↔ _
  rw [LocalClassFieldTheory.abelianLocalArtinMap_ker]
  rfl

/-- The same local symbol viewed as an actual global automorphism. -/
def localArtin (w : Place k L) : (w.restrict K).adicCompletionˣ →* Gal(L/K) :=
  (IdeleGroup.decompositionGroup (K := K) w).subtype.comp
    (localDecompositionArtin (K := K) w).toMonoidHom

/-- The image of the local symbol is exactly the actual decomposition subgroup. -/
theorem localArtin_range (w : Place k L) :
    (localArtin (K := K) w).range = IdeleGroup.decompositionGroup (K := K) w := by
  apply le_antisymm
  · rintro σ ⟨x, rfl⟩
    exact (localDecompositionArtin (K := K) w x).property
  · intro σ hσ
    obtain ⟨x, hx⟩ := localDecompositionArtin_surjective (K := K) w ⟨σ, hσ⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Triviality of the global-valued local symbol detects actual local norms. -/
theorem localArtin_eq_one_iff (w : Place k L) (x : (w.restrict K).adicCompletionˣ) :
    localArtin (K := K) w x = 1 ↔ x ∈ (IdeleGroup.localNorm (K := K) w).range := by
  change ((localDecompositionArtin (K := K) w x :
    IdeleGroup.decompositionGroup (K := K) w) : Gal(L/K)) = 1 ↔ _
  rw [← Subgroup.coe_one (IdeleGroup.decompositionGroup (K := K) w), Subtype.val_inj]
  change x ∈ (localDecompositionArtin (K := K) w).toMonoidHom.ker ↔ _
  rw [localDecompositionArtin_ker]

end FunctionField
