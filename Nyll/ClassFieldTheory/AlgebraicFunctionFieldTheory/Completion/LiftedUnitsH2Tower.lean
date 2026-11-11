/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LiftedUnitsH2Over
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2

/-!
# Localized lifted unit H² in an actual function-field tower

The actual completion maps form a commuting scalar tower. Naturality of unit
inflation and injectivity of finite local inflation therefore identify the
vanishing of a localized class before and after global inflation.
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology
open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k : Type u} {K : Type v} {L M : Type w}
    [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    [IsGalois K L] [IsGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- At an actual place of a finite Galois tower, local vanishing is preserved
and reflected by inflation from the lower global extension. -/
theorem liftedCompletionUnitsH2Map_inflation_eq_zero_iff
    (u : Place k M) (c : groupCohomology (liftedGaloisUnitsRep K L) 2) :
    liftedCompletionUnitsH2Map (K := K) (u.restrict L) c = 0 ↔
      liftedCompletionUnitsH2Map (K := K) u (liftedFiniteGaloisTowerUnitsH2Inflation K L M c) = 0
        := by
  let w := u.restrict L
  let v := w.restrict K
  have huv : u.restrict K = v := (restrict_restrict (F := K) (E := L) u).symm
  let avw : Algebra v.adicCompletion w.adicCompletion := (completionMapOver v w rfl).toAlgebra
  let awu : Algebra w.adicCompletion u.adicCompletion := (completionMapOver w u rfl).toAlgebra
  let avu : Algebra v.adicCompletion u.adicCompletion := (completionMapOver v u huv).toAlgebra
  let aKw : Algebra K w.adicCompletion :=
    ((algebraMap L w.adicCompletion).comp (algebraMap K L)).toAlgebra
  let aKu : Algebra K u.adicCompletion :=
    ((algebraMap M u.adicCompletion).comp (algebraMap K M)).toAlgebra
  let aLu : Algebra L u.adicCompletion :=
    ((algebraMap M u.adicCompletion).comp (algebraMap L M)).toAlgebra
  have hKM : IsScalarTower K M u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hLM : IsScalarTower L M u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKLw : IsScalarTower K L w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKLu : IsScalarTower K L u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      congrArg (algebraMap M u.adicCompletion) (IsScalarTower.algebraMap_apply K L M x))
  have hKvw : IsScalarTower K v.adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun x => (completionMapOver_algebraMap v w rfl x).symm)
  have hKvu : IsScalarTower K v.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun x => (completionMapOver_algebraMap v u huv x).symm)
  have hLwu : IsScalarTower L w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun x => (completionMapOver_algebraMap w u rfl x).symm)
  have hKwu : IsScalarTower K w.adicCompletion u.adicCompletion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap M u.adicCompletion (algebraMap K M x) =
      completionMapOver w u rfl (algebraMap L w.adicCompletion (algebraMap K L x))
    rw [completionMapOver_algebraMap, ← IsScalarTower.algebraMap_apply K L M]
  have hvwu : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f x)
        (completionMapOver_trans v w u rfl rfl huv)).symm)
  have hfinite : FiniteDimensional v.adicCompletion u.adicCompletion :=
    (completionFiniteGaloisOver v u huv).1
  have hgalois : IsGalois v.adicCompletion u.adicCompletion :=
    (completionFiniteGaloisOver v u huv).2
  have hwgalois : IsGalois v.adicCompletion w.adicCompletion :=
    (completionFiniteGaloisOver v w rfl).2
  have hbase := liftedFiniteGaloisTowerUnitsH2BaseChange_trans
    K L v.adicCompletion w.adicCompletion u.adicCompletion
  have hglob := liftedFiniteGaloisTowerUnitsH2Inflation_trans K L M u.adicCompletion
  have hupper := liftedCompletionUnitsH2MapOver_eq_inflation_restriction v u huv
  have hlower := liftedCompletionUnitsH2MapOver_eq_inflation_restriction v w rfl
  have hsquare :
      liftedCompletionUnitsH2MapOver v w rfl ≫
          liftedFiniteGaloisTowerUnitsH2Inflation v.adicCompletion w.adicCompletion
            u.adicCompletion =
        liftedFiniteGaloisTowerUnitsH2Inflation K L M ≫ liftedCompletionUnitsH2MapOver v u huv := by
    rw [hlower, hupper, hbase, ← hglob, Category.assoc]
  have heval := congrArg
    (fun (f : groupCohomology (liftedGaloisUnitsRep K L) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep v.adicCompletion u.adicCompletion) 2) => f c) hsquare
  change liftedFiniteGaloisTowerUnitsH2Inflation v.adicCompletion w.adicCompletion u.adicCompletion
      (liftedCompletionUnitsH2MapOver v w rfl c) =
    liftedCompletionUnitsH2MapOver v u huv
      (liftedFiniteGaloisTowerUnitsH2Inflation K L M c) at heval
  have hinj := liftedFiniteGaloisTowerUnitsH2Inflation_injective
    v.adicCompletion w.adicCompletion u.adicCompletion
  have heq : liftedCompletionUnitsH2MapOver v w rfl c = 0 ↔
      liftedCompletionUnitsH2MapOver v u huv (liftedFiniteGaloisTowerUnitsH2Inflation K L M c) = 0
        := by
    constructor
    · intro hc
      exact heval.symm.trans (by rw [hc, map_zero])
    · intro hc
      apply hinj
      exact (heval.trans hc).trans (map_zero _).symm
  exact (liftedCompletionUnitsH2MapOver_eq_zero_iff v w rfl c).symm.trans
    (heq.trans (liftedCompletionUnitsH2MapOver_eq_zero_iff v u huv
      (liftedFiniteGaloisTowerUnitsH2Inflation K L M c)))

end FunctionField.IdeleGroup
