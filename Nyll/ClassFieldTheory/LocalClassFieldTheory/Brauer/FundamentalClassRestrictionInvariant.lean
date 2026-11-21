/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteStageRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClass

/-! # The invariant of the restricted local fundamental class -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology
open ClassFieldTower.Cohomology LocalFieldTheory Module
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

attribute [local instance] stageSeparableClosureAlgebra

variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section SubgroupRestriction

variable (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
  (h : F ≤ E.toIntermediateField) (j : (SeparableClosure K) ≃ₐ[F] SeparableClosure F)

/-- Restriction of the local fundamental class to an actual intermediate
base has arithmetic invariant the reciprocal of the remaining degree. -/
theorem localFundamentalClass_restriction_invariant :
    let : Algebra F (↥E.toIntermediateField) := nestedStageAlgebra F E h
    let : IsScalarTower K F (↥E.toIntermediateField) := nestedStageTower F E h
    let : FiniteDimensional F (↥E.toIntermediateField) := nestedStageFinite F E h
    let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
    let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
    let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
    localBrauerInvariant F (relativeStageAbsoluteInflation F E h j
      (relativeBaseRestriction K F E (localFundamentalClass K E))) =
      (((1 : ℚ) / (finrank F E : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
  intro algebraOwner towerOwner finiteOwner normOwner valuationOwner localFieldOwner
  rw [← embeddedAbsoluteBrRestriction_finiteInflation F E h j,
    localBrauerInvariant_embeddedRestriction]
  change finrank K F • relativeLocalBrauerInvariant K E (localFundamentalClass K E) = _
  rw [relativeLocalBrauerInvariant_fundamentalClass, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  apply congrArg (fun z : ℚ => (z : AddCircle (1 : ℚ)))
  let : Module.Free F (↥E.toIntermediateField) :=
    Module.Free.of_divisionRing (K := F) (V := ↥E.toIntermediateField)
  have hDegree : finrank K F * finrank F E = finrank K E :=
    Module.finrank_mul_finrank K F (↥E.toIntermediateField)
  have hm : (finrank K F : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < finrank K F).ne'
  rw [← hDegree, Nat.cast_mul, mul_one_div]
  simpa only [mul_one] using mul_div_mul_left (1 : ℚ) (finrank F E : ℚ) hm

end SubgroupRestriction

end ClassFieldTheory.Brauer
