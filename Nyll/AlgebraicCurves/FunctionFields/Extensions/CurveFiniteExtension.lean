/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendental
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental

/-!
# Curve structure on an actual finite extension

A separating parameter of the base curve gives a finite transcendental
presentation upstairs. The perfect-field separating-parameter theorem
then supplies the curve structure and its principal divisors.
-/

@[expose] public section

namespace AlgebraicCurve

/-- A finite extension of a one-variable function field has an actual separating
transcendental parameter. -/
theorem exists_separating_transcendental_over_finite_extension
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [FiniteDimensional F L] :
    ∃ y : L, Transcendental K y ∧
      FiniteDimensional (IntermediateField.adjoin K ({y} : Set L)) L ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({y} : Set L)) L := by
  have : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := hfin
  have : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) L :=
    Module.Finite.trans F L
  have hfinL : FiniteDimensional
      (IntermediateField.adjoin K ({algebraMap F L x} : Set L)) L :=
    .of_restrictScalars_finite (IntermediateField.adjoin K ({x} : Set F)) _ _
  have hxL : Transcendental K (algebraMap F L x) :=
    (transcendental_algebraMap_iff (algebraMap F L).injective).mpr hx
  exact exists_separating_transcendental_of_perfectField hxL hfinL

/-- A finite extension of the given curve function field is itself a
curve function field over the same algebraically closed constants. -/
theorem IsCurveOver.of_finite_extension
    (K F L : Type*) [Field K] [IsAlgClosed K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] [FiniteDimensional F L] :
    IsCurveOver K L := by
  obtain ⟨x, hx, hfinite, _⟩ := IsCurveOver.exists_separating_transcendental
    (K := K) (F := F)
  obtain ⟨y, hy, hfiniteL, hsepL⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfinite L
  exact isCurveOver_of_transcendental hy hfiniteL hsepL

end AlgebraicCurve
