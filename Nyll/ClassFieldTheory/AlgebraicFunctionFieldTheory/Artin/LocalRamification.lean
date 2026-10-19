/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
import Nyll.ValuedFieldTheory.Ramification.Filtration
import Nyll.ValuedFieldTheory.Ramification.LocalField.Core

/-!
# Higher units and ramification under the function-field local symbol

The arithmetic inversion in the function-field convention preserves each
higher-unit subgroup. The completed local symbol therefore carries precisely
the existing higher units onto the existing upper ramification groups.
The same actual local norm kernel gives the minimal conductor cutoff.
-/

open scoped AlgebraicCurve.Place

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Higher-unit images under the arithmetic local symbol are the actual
completed upper ramification groups, at every nonnegative integer depth. -/
theorem localDecompositionArtin_higherUnits_completion (w : Place k L) (n : ℕ) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    ((RayClass.localHigherUnitGroup (w.restrict K) n).map
      (localDecompositionArtin (K := K) w).toMonoidHom).map
        (IdeleGroup.decompositionCompletionEquiv (K := K) w).toMonoidHom =
      RamificationTheory.LocalField.localUpperRamificationGroup
        (w.restrict K).adicCompletion w.adicCompletion (n : ℝ) := by
  intro hrelation hlocal
  have hmap :
      ((RayClass.localHigherUnitGroup (w.restrict K) n).map
        (localDecompositionArtin (K := K) w).toMonoidHom).map
          (IdeleGroup.decompositionCompletionEquiv (K := K) w).toMonoidHom =
        LocalClassFieldTheory.artinPrincipalUnitGroup
          (w.restrict K).adicCompletion w.adicCompletion n := by
    rw [Subgroup.map_map]
    apply Subgroup.ext
    intro σ
    constructor
    · rintro ⟨x, hx, hσ⟩
      refine ⟨x⁻¹, (RayClass.localHigherUnitGroup (w.restrict K) n).inv_mem hx, ?_⟩
      exact (localDecompositionArtin_completion (K := K) w x).symm.trans hσ
    · rintro ⟨x, hx, hσ⟩
      refine ⟨x⁻¹, (RayClass.localHigherUnitGroup (w.restrict K) n).inv_mem hx, ?_⟩
      change IdeleGroup.decompositionCompletionEquiv (K := K) w
        (localDecompositionArtin (K := K) w x⁻¹) = σ
      rw [localDecompositionArtin_completion, inv_inv]
      exact hσ
  rw [hmap]
  have hfiltered := LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
    (w.restrict K).adicCompletion w.adicCompletion (n : ℝ) (Nat.cast_nonneg n)
  simpa only [LocalClassFieldTheory.artinPrincipalUnitStepGroup,
    RamificationTheory.natCeilStepFiltration, Nat.ceil_natCast] using hfiltered

/-- The conductor exponent of the actual completed extension is the least
depth on which the function-field local Artin symbol is trivial. -/
theorem localConductorExponent_le_iff_localArtin (w : Place k L) (n : ℕ) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    LocalClassFieldTheory.localConductorExponent
        (w.restrict K).adicCompletion w.adicCompletion ≤ n ↔
      ∀ x ∈ RayClass.localHigherUnitGroup (w.restrict K) n,
        localArtin (K := K) w x = 1 := by
  intro hrelation hlocal
  rw [LocalClassFieldTheory.localConductorExponent_le_iff]
  constructor
  · intro h x hx
    exact (localArtin_eq_one_iff (K := K) w x).mpr (h hx)
  · intro h x hx
    exact (localArtin_eq_one_iff (K := K) w x).mp (h x hx)

end FunctionField
