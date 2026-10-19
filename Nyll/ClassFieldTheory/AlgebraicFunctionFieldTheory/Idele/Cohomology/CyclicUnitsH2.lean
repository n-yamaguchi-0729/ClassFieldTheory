/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantH2Descent
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2Tower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ConstantUnitsH2
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq

/-!
# The local-global principle for cyclic unit H²

Tsen and finite constant descent put a cyclic class into a finite constant
extension after inflation to the actual compositum. Local inflation detects
vanishing, so the constant-extension local-global theorem kills that class.
Injectivity of global inflation then kills the original class.
-/

noncomputable section

open AlgebraicCurve

namespace FunctionField

open ClassFieldTower.Cohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- The actual completions detect every unit H² class of a finite cyclic stage. -/
theorem cyclicUnitsH2_eq_zero_of_forall_completion
    (L : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hc : ∀ w : Place k L, IdeleGroup.completionUnitsH2Map (K := K) w c = 0) :
    c = 0 := by
  obtain ⟨n, hn⟩ := exists_fullConstantDegreeStage_H2_constant_inflation k K Ω L c
  let C := (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField
  let N := IntermediateField.adjoin C (L.toIntermediateField : Set Ω)
  let aLN : Algebra L N := (FieldTheory.compositumEmbedding L.toIntermediateField C).toAlgebra
  have hKLN : IsScalarTower K L N :=
    FieldTheory.compositumScalarTower L.toIntermediateField C
  have hprops := FieldTheory.finiteGalois_adjoin_intermediateField L.toIntermediateField C
  have hfin : FiniteDimensional K N := hprops.1
  have hgal : IsGalois K N := hprops.2
  have hLfin : FiniteDimensional L N := FiniteDimensional.right K L N
  have hCfin : FiniteDimensional C N := FiniteDimensional.right K C N
  have hCgal : IsGalois C N := IsGalois.tower_top_of_isGalois K C N
  let akN : Algebra k N := ((algebraMap K N).comp (algebraMap k K)).toAlgebra
  let aRN : Algebra (RatFunc k) N :=
    ((algebraMap K N).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKN : IsScalarTower k K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKN : IsScalarTower (RatFunc k) K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkCN : IsScalarTower k C N := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap K N (algebraMap k K x) = algebraMap C N (algebraMap k C x)
    rw [IsScalarTower.algebraMap_apply k K C, ← IsScalarTower.algebraMap_apply K C N])
  have hkLN : IsScalarTower k L N :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change algebraMap K N (algebraMap k K x) = algebraMap L N (algebraMap k L x)
      rw [IsScalarTower.algebraMap_apply k K L, ← IsScalarTower.algebraMap_apply K L N])
  have hkRN : IsScalarTower k (RatFunc k) N :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      congrArg (algebraMap K N) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  have hff : FunctionField k N := Module.Finite.trans K N
  have hcurve : IsCurveOver k N := FunctionField.isCurveOver k N
  obtain ⟨d, hd⟩ := hn
  have hdlocal : ∀ w : Place k C, IdeleGroup.completionUnitsH2Map (K := K) w d = 0 := by
    intro w
    obtain ⟨u, hu⟩ := Place.exists_restrict_eq (M := N) w
    have hclocal := (IdeleGroup.completionUnitsH2Map_inflation_eq_zero_iff
      (K := K) (L := L) u c).mp (hc (u.restrict L))
    have hdlocal := (IdeleGroup.completionUnitsH2Map_inflation_eq_zero_iff
      (K := K) (L := C) u d).mpr (by rw [hd]; exact hclocal)
    exact hu ▸ hdlocal
  have hdzero := constantUnitsH2_eq_zero_of_forall_completion k K Ω (n : ℕ) d hdlocal
  apply finiteGaloisTowerUnitsH2Inflation_injective K L N
  exact hd.symm.trans ((congrArg (finiteGaloisTowerUnitsH2Inflation K C N) hdzero).trans
    ((map_zero _).trans (map_zero _).symm))

end FunctionField
