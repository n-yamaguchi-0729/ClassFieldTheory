/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Representation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOne

/-!
# Actual base idele classes and the distinguished fixed module

The field and its image in the ambient Galois closure have degree one.
Their actual idele-class base change followed by fixed-field descent
identifies the original class group with the distinguished fixed coefficients.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The original function-field idele classes are precisely the distinguished fixed coefficients. -/
def baseClassEquiv :
    let _ : AlgebraicCurve.IsCurveOver k K := isCurveOver k K
    Additive (IdeleClassGroup k K) ≃+
      ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) (baseField Gal(Ω/K)) := by
  intro hcurve
  have hE : FiniteDimensional K (abstractFixedField K Ω (baseField Gal(Ω/K))) :=
    abstractFixedField_finiteDimensional K Ω _ (FiniteAbstractField.base Gal(Ω/K)).finite
  have hbot : abstractFixedField K Ω (baseField Gal(Ω/K)) = ⊥ := InfiniteGalois.fixedField_bot
  let e : abstractFixedField K Ω (baseField Gal(Ω/K)) ≃ₐ[K] K :=
    (IntermediateField.equivOfEq hbot).trans (IntermediateField.botEquiv K Ω)
  have hgal : IsGalois K (abstractFixedField K Ω (baseField Gal(Ω/K))) :=
    IsGalois.of_algEquiv e.symm
  have hdegree : Module.finrank K (abstractFixedField K Ω (baseField Gal(Ω/K))) = 1 := by
    rw [hbot, IntermediateField.finrank_bot]
  exact (MulEquiv.toAdditive (IdeleClassGroup.baseChangeEquivOfFinrankOne (k := k) hdegree)).trans
    (abstractFixedClassEquiv k K Ω (baseField Gal(Ω/K)) (FiniteAbstractField.base Gal(Ω/K)).finite)

end FunctionField
