/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Kummer
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateNakayama
public import Nyll.GaloisCohomology.Topology.DiscreteGroupComparison

/-! # Third cohomology of local units and the original Kummer coefficients -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory CategoryTheory.Limits TopRep ContinuousCohomology LocalFieldTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "Stage" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- Tate–Nakayama computes degree three of the actual finite-stage continuous unit complexes. -/
theorem relativeLocalUnitsH3_eq_zero (E : Stage) (x : continuousCohomology 3 (galoisUnitsRep K E)) :
    x = 0 := by
  let A := Rep.ofAlgebraAutOnUnits K E
  let h := localUnitsH3_isZero K E E.toIntermediateField.val
  let i := IntegralGroupCohomology.Universe.cohomologyIsoCommon A 3
  have h₀ : IsZero (IntegralGroupCohomology.cohomology A 3) := IsZero.of_iso h i.symm
  let e := discreteIntegralCohomologyEquiv (galoisUnitsRep K E) 3
  have hz : e x = 0 := ConcreteCategory.congr_hom (h₀.eq_of_tgt (𝟙 _) 0) (e x)
  exact e.injective (hz.trans e.map_zero.symm)

/-- An absolute unit class in degree three already has a finite local
representative, which is zero by Tate–Nakayama. -/
theorem absoluteLocalUnitsH3_eq_zero (x : continuousCohomology 3 (unitsRep K)) : x = 0 := by
  obtain ⟨E, y, hy⟩ := exists_finiteDegreeInflation_eq 3 x
  let inflate := finiteDegreeInflation E 3
  have hy0 : y = 0 := relativeLocalUnitsH3_eq_zero K E y
  exact hy.symm.trans ((congrArg inflate hy0).trans (map_zero inflate))

/-- Actual continuous local Kummer cohomology vanishes in degree three
for every exponent invertible in the field. -/
theorem localKummerH3_eq_zero (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (x : continuousCohomology 3 (separableMuTopRep K n)) : x = 0 :=
  separableMuH3_eq_zero_of_units K n hn (localBrauer_nsmul_surjective K n n.pos)
    (absoluteLocalUnitsH3_eq_zero K) x

end ClassFieldTheory.Brauer
