/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2

/-!
# Naturality of actual field-unit H² in towers

These identities compare restriction of actual field automorphisms and the
specified inclusions of units. They also apply when the final field is a
completion, without requiring it to be finite over the original global field.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

/-- Successive actual unit inflations equal direct inflation along the field tower. -/
theorem finiteGaloisTowerUnitsH2Inflation_trans
    (K F M N : Type) [Field K] [Field F] [Field M] [Field N]
    [Algebra K F] [Algebra K M] [Algebra K N]
    [Algebra F M] [Algebra F N] [Algebra M N]
    [IsScalarTower K F M] [IsScalarTower K F N] [IsScalarTower K M N]
    [IsScalarTower F M N] [Normal K F] [Normal K M] :
    finiteGaloisTowerUnitsH2Inflation K F M ≫ finiteGaloisTowerUnitsH2Inflation K M N =
      finiteGaloisTowerUnitsH2Inflation K F N := by
  rw [finiteGaloisTowerUnitsH2Inflation, finiteGaloisTowerUnitsH2Inflation,
    finiteGaloisTowerUnitsH2Inflation, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    calc
      algebraMap F N ((σ.restrictNormal M).restrictNormal F x) =
          algebraMap M N (algebraMap F M ((σ.restrictNormal M).restrictNormal F x)) :=
        IsScalarTower.algebraMap_apply F M N _
      _ = algebraMap M N ((σ.restrictNormal M) (algebraMap F M x)) :=
        congrArg (algebraMap M N) ((σ.restrictNormal M).restrictNormal_commutes F x)
      _ = σ (algebraMap M N (algebraMap F M x)) :=
        σ.restrictNormal_commutes M (algebraMap F M x)
      _ = σ (algebraMap F N x) :=
        congrArg σ (IsScalarTower.algebraMap_apply F M N x).symm
      _ = algebraMap F N (σ.restrictNormal F x) := (σ.restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F M N ((show Additive Fˣ from a).toMul : F)).symm

/-- Localization through an intermediate normal upper field agrees with direct
localization. The intermediate upper field need not be normal over the original base. -/
theorem finiteGaloisTowerUnitsH2BaseChange_trans
    (K F E M N : Type) [Field K] [Field F] [Field E] [Field M] [Field N]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra K N]
    [Algebra F M] [Algebra F N] [Algebra E M] [Algebra E N] [Algebra M N]
    [IsScalarTower K F M] [IsScalarTower K F N] [IsScalarTower K M N]
    [IsScalarTower K E M] [IsScalarTower K E N]
    [IsScalarTower F M N] [IsScalarTower E M N] [Normal K F] [Normal E M] :
    (finiteGaloisTowerUnitsH2Inflation K F M ≫ finiteGaloisTowerUnitsH2Restriction K E M) ≫
        finiteGaloisTowerUnitsH2Inflation E M N =
      finiteGaloisTowerUnitsH2Inflation K F N ≫ finiteGaloisTowerUnitsH2Restriction K E N := by
  simp only [finiteGaloisTowerUnitsH2Inflation, finiteGaloisTowerUnitsH2Restriction]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    calc
      algebraMap F N (((σ.restrictNormal M).restrictScalars K).restrictNormal F x) =
          algebraMap M N (algebraMap F M
            (((σ.restrictNormal M).restrictScalars K).restrictNormal F x)) :=
        IsScalarTower.algebraMap_apply F M N _
      _ = algebraMap M N ((σ.restrictNormal M) (algebraMap F M x)) :=
        congrArg (algebraMap M N)
          (((σ.restrictNormal M).restrictScalars K).restrictNormal_commutes F x)
      _ = σ (algebraMap M N (algebraMap F M x)) :=
        σ.restrictNormal_commutes M (algebraMap F M x)
      _ = σ (algebraMap F N x) :=
        congrArg σ (IsScalarTower.algebraMap_apply F M N x).symm
      _ = algebraMap F N ((σ.restrictScalars K).restrictNormal F x) :=
        ((σ.restrictScalars K).restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F M N ((show Additive Fˣ from a).toMul : F)).symm

end
end ClassFieldTower.Cohomology
