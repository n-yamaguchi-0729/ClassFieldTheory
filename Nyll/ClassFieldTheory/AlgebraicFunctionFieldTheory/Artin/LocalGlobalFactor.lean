/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.OnePlaceNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Factoring the one-place global Artin map through local reciprocity

The completed norm kernel maps into the actual global class-norm kernel.
Thus the global Artin map on a one-place idele factors uniquely through the
local Artin map onto the actual decomposition group. Identifying this factor
with the subgroup inclusion requires the further Frobenius comparison.
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

/-- A completed local norm has trivial global Artin symbol after one-place insertion. -/
theorem abelianFiniteArtin_placeIdele_eq_one_of_mem_localNorm (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : x ∈ (IdeleGroup.localNorm (K := K) w).range) :
    abelianFiniteArtin k K L
      (QuotientGroup.mk (IdeleGroup.placeIdele (w.restrict K) x)) = 1 := by
  apply (abelianFiniteArtin_eq_one_iff_mem_norm k K L _).2
  exact IdeleClassGroup.placeIdele_mk_mem_norm_range w x hx

/-- The actual local reciprocity kernel lies in the one-place global reciprocity kernel. -/
theorem localDecompositionArtin_ker_le (w : Place k L) :
    (localDecompositionArtin (K := K) w).toMonoidHom.ker ≤
      ((abelianFiniteArtin k K L).comp
        ((QuotientGroup.mk' (IdeleGroup.principalSubgroup k K)).comp
          (IdeleGroup.placeIdele (w.restrict K)))).ker := by
  intro x hx
  rw [localDecompositionArtin_ker] at hx
  exact abelianFiniteArtin_placeIdele_eq_one_of_mem_localNorm w x hx

/-- The global Artin value on a one-place idele, factored through actual local reciprocity. -/
def localGlobalArtinFactor (w : Place k L) :
    IdeleGroup.decompositionGroup (K := K) w →* Gal(L/K) :=
  (localDecompositionArtin (K := K) w).toMonoidHom.liftOfSurjective
    (localDecompositionArtin_surjective w)
    ⟨(abelianFiniteArtin k K L).comp
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup k K)).comp
        (IdeleGroup.placeIdele (w.restrict K))), localDecompositionArtin_ker_le w⟩

/-- Evaluating the factor on a local Artin symbol recovers the original global symbol. -/
theorem localGlobalArtinFactor_apply_localDecompositionArtin (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    localGlobalArtinFactor w (localDecompositionArtin (K := K) w x) =
      abelianFiniteArtin k K L
        (QuotientGroup.mk (IdeleGroup.placeIdele (w.restrict K) x)) := by
  exact MonoidHom.liftOfRightInverse_comp_apply
    (localDecompositionArtin (K := K) w).toMonoidHom
    (Function.surjInv (localDecompositionArtin_surjective w))
    (Function.rightInverse_surjInv (localDecompositionArtin_surjective w))
    ⟨(abelianFiniteArtin k K L).comp
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup k K)).comp
        (IdeleGroup.placeIdele (w.restrict K))), localDecompositionArtin_ker_le w⟩ x

/-- Local reciprocity determines the one-place factor uniquely. -/
theorem localGlobalArtinFactor_unique (w : Place k L)
    (f : IdeleGroup.decompositionGroup (K := K) w →* Gal(L/K))
    (hf : ∀ x : (w.restrict K).adicCompletionˣ,
      f (localDecompositionArtin (K := K) w x) =
        abelianFiniteArtin k K L
          (QuotientGroup.mk (IdeleGroup.placeIdele (w.restrict K) x))) :
    f = localGlobalArtinFactor w := by
  apply MonoidHom.ext
  intro σ
  obtain ⟨x, rfl⟩ := localDecompositionArtin_surjective w σ
  exact (hf x).trans (localGlobalArtinFactor_apply_localDecompositionArtin w x).symm

end FunctionField
