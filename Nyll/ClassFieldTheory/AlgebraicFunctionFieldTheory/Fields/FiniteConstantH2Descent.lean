/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantNormDescent
import Nyll.GaloisCohomology.FieldTheory.CompositumCyclic
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormClass

/-!
# Finite constant descent of cyclic unit H²

Every actual unit H² class of a finite cyclic function-field extension vanishes
after base change to a constructed finite constant extension. The field norm
preimage is supplied by Tsen and its finite-stage descent.
-/

noncomputable section

namespace FunctionField

open IntermediateField ClassFieldTower.Cohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- A cyclic unit H² class becomes zero over some actual finite constant stage. -/
theorem exists_fullConstantDegreeStage_H2_inflation_restriction_zero
    (L : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ n : ℕ+,
      let C := (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField
      let N := adjoin C (L.toIntermediateField : Set Ω)
      let _ : Algebra L N := (FieldTheory.compositumEmbedding L.toIntermediateField C).toAlgebra
      let _ : IsScalarTower K L N := FieldTheory.compositumScalarTower L.toIntermediateField C
      finiteGaloisTowerUnitsH2Restriction K C N
        (finiteGaloisTowerUnitsH2Inflation K L N c) = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨a, rfl⟩ := finiteCyclicBaseUnitH2Class_surjective K L g hg c
  obtain ⟨n, x, hx⟩ := exists_fullConstantDegreeStage_compositum_norm_preimage
    k K Ω L.toIntermediateField (a : K)
  refine ⟨n, ?_⟩
  intro C N algL towerL
  have hprops := FieldTheory.finiteGalois_adjoin_intermediateField L.toIntermediateField C
  have hfin : FiniteDimensional K N := hprops.1
  have hgal : IsGalois K N := hprops.2
  have hrelfin : FiniteDimensional C N := FiniteDimensional.right K C N
  have hrelgal : IsGalois C N := IsGalois.tower_top_of_isGalois K C N
  have hcyc : IsCyclic Gal(N/C) :=
    FieldTheory.isCyclic_adjoin_intermediateField L.toIntermediateField C
  exact finiteCyclicBaseUnitH2Class_inflation_restriction_eq_zero_of_norm K L C N g hg a x hx

/-- Every cyclic unit H² class comes from a finite constant extension after
inflation to the actual common compositum. -/
theorem exists_fullConstantDegreeStage_H2_constant_inflation
    (L : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ n : ℕ+,
      let C := (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField
      let N := adjoin C (L.toIntermediateField : Set Ω)
      let _ : Algebra L N := (FieldTheory.compositumEmbedding L.toIntermediateField C).toAlgebra
      let _ : IsScalarTower K L N := FieldTheory.compositumScalarTower L.toIntermediateField C
      ∃ d : groupCohomology (Rep.ofAlgebraAutOnUnits K C) 2,
        finiteGaloisTowerUnitsH2Inflation K C N d =
          finiteGaloisTowerUnitsH2Inflation K L N c := by
  obtain ⟨n, hn⟩ := exists_fullConstantDegreeStage_H2_inflation_restriction_zero k K Ω L c
  refine ⟨n, ?_⟩
  intro C N algL towerL
  have hprops := FieldTheory.finiteGalois_adjoin_intermediateField L.toIntermediateField C
  have hfin : FiniteDimensional K N := hprops.1
  have hgal : IsGalois K N := hprops.2
  exact finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range K C N hn

end FunctionField
