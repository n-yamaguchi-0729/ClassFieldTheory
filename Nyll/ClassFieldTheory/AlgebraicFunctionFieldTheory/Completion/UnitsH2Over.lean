/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower

/-!
# Completed unit H² over a specified base place

The base place can be identified by a supplied restriction equality. This uses
the existing completion map over that equality and permits compatible scalar
towers when several intermediate fields occur.
-/

noncomputable section

open CategoryTheory AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual completed extension over any identified base place is finite Galois. -/
theorem completionFiniteGaloisOver [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    FiniteDimensional v.adicCompletion w.adicCompletion ∧
      IsGalois v.adicCompletion w.adicCompletion := by
  have hf : FiniteDimensional (w.restrict K).adicCompletion w.adicCompletion := inferInstance
  have hg : IsGalois (w.restrict K).adicCompletion w.adicCompletion := inferInstance
  subst v
  exact ⟨hf, hg⟩

/-- The actual unit localization map with the base place identified by its restriction. -/
def completionUnitsH2MapOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits v.adicCompletion w.adicCompletion) 2 := by
  subst v
  exact completionUnitsH2Map (K := K) w

/-- Transporting only the base place preserves the vanishing of an actual localized class. -/
theorem completionUnitsH2MapOver_eq_zero_iff (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) (c : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    completionUnitsH2MapOver v w hw c = 0 ↔ completionUnitsH2Map (K := K) w c = 0 := by
  subst v
  exact Iff.rfl

/-- The transported localization is still the actual inclusion followed by relative restriction. -/
theorem completionUnitsH2MapOver_eq_inflation_restriction
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    let _ : Algebra K w.adicCompletion :=
      ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L w.adicCompletion :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower K v.adicCompletion w.adicCompletion :=
      IsScalarTower.of_algebraMap_eq (fun x => (completionMapOver_algebraMap v w hw x).symm)
    completionUnitsH2MapOver v w hw =
      finiteGaloisTowerUnitsH2Inflation K L w.adicCompletion ≫
        finiteGaloisTowerUnitsH2Restriction K v.adicCompletion w.adicCompletion := by
  subst v
  rfl

end FunctionField.IdeleGroup
