/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteStageRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClass

/-! # Inflation of the local fundamental class in a finite tower -/

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

section Tower

variable (T : FiniteGaloisIntermediateField K (SeparableClosure K))
  (h : E.toIntermediateField ≤ T.toIntermediateField)

/-- Inflation sends the arithmetic fundamental class to the upper class
multiplied by the actual relative extension degree. -/
theorem relativeInflation_localFundamentalClass :
    let : Algebra (↥E.toIntermediateField) (↥T.toIntermediateField) :=
      nestedStageAlgebra E.toIntermediateField T h
    let : IsScalarTower K (↥E.toIntermediateField) (↥T.toIntermediateField) :=
      nestedStageTower E.toIntermediateField T h
    relativeInflation K E T (localFundamentalClass K E) =
      finrank E T • localFundamentalClass K T := by
  intro algebraOwner towerOwner
  let : FiniteDimensional (↥E.toIntermediateField) (↥T.toIntermediateField) :=
    nestedStageFinite E.toIntermediateField T h
  apply finiteInflation_injective T
  apply (localBrauerInvariantEquiv K).injective
  rw [finiteInflation_tower E T (fun _ => rfl), map_nsmul (finiteInflation T),
    map_nsmul (localBrauerInvariantEquiv K)]
  change relativeLocalBrauerInvariant K E (localFundamentalClass K E) =
    finrank E T • relativeLocalBrauerInvariant K T (localFundamentalClass K T)
  rw [relativeLocalBrauerInvariant_fundamentalClass, relativeLocalBrauerInvariant_fundamentalClass,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  apply congrArg (fun z : ℚ => (z : AddCircle (1 : ℚ)))
  rw [← mul_div_assoc, mul_one]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < finrank K T).ne')).2
  let : Module.Free (↥E.toIntermediateField) (↥T.toIntermediateField) :=
    Module.Free.of_divisionRing (K := ↥E.toIntermediateField) (V := ↥T.toIntermediateField)
  have hDegree : finrank K E * finrank E T = finrank K T :=
    Module.finrank_mul_finrank K (↥E.toIntermediateField) (↥T.toIntermediateField)
  have hm : (finrank K E : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < finrank K E).ne'
  rw [← hDegree, Nat.cast_mul, ← mul_assoc, div_mul_cancel₀ _ hm, one_mul]

end Tower

end ClassFieldTheory.Brauer
