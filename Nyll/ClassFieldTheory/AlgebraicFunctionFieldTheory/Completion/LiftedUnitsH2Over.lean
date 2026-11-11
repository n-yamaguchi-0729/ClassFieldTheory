/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LiftedUnitsH2
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2Over
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2

/-!
# Lifted unit H² over the specified actual base place

The original completionMapOver supplies every algebra structure. Only the
coefficient scalar ring used to form the cohomology objects is transported.
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual unit localization map with the base place identified by its restriction. -/
def liftedCompletionUnitsH2MapOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    groupCohomology (liftedGaloisUnitsRep K L) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep v.adicCompletion w.adicCompletion) 2 := by
  subst v
  exact liftedCompletionUnitsH2Map (K := K) w

/-- Transporting only the base place preserves the vanishing of an actual localized class. -/
theorem liftedCompletionUnitsH2MapOver_eq_zero_iff (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) (c : groupCohomology (liftedGaloisUnitsRep K L) 2) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    liftedCompletionUnitsH2MapOver v w hw c = 0 ↔ liftedCompletionUnitsH2Map (K := K) w c = 0 := by
  subst v
  exact Iff.rfl

/-- The transported localization is still the actual inclusion followed by relative restriction. -/
theorem liftedCompletionUnitsH2MapOver_eq_inflation_restriction
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w hw).toAlgebra
    let _ : Algebra K w.adicCompletion :=
      ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L w.adicCompletion :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower K v.adicCompletion w.adicCompletion :=
      IsScalarTower.of_algebraMap_eq (fun x => (completionMapOver_algebraMap v w hw x).symm)
    liftedCompletionUnitsH2MapOver v w hw =
      liftedFiniteGaloisTowerUnitsH2Inflation K L w.adicCompletion ≫
        liftedFiniteGaloisTowerUnitsH2Restriction K v.adicCompletion w.adicCompletion := by
  subst v
  rfl

end FunctionField.IdeleGroup
