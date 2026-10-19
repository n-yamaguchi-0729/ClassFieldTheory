/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.RationalDegreeFixed
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation

/-!
# Actual degree of the abstract norm to the base

The finite coset cardinal is the actual fixed-field degree. It cancels the
denominator in the rational degree, so the actual abstract norm to the base
has precisely the ordinary degree of the represented upper-field idele class.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

/-- The base-relative coset cardinal is the actual fixed-field degree,
including nonnormal fields. -/
theorem abstractFixedField_finrank_eq_card (K Ω : Type) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (H : ClosedSubgroup Gal(Ω/K)) :
    Module.finrank K (abstractFixedField K Ω H) =
      Nat.card ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    InfiniteGalois.fixingSubgroup_fixedField H]
  change H.toSubgroup.index = (extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H)).index
  rw [← Subgroup.relIndex_top_right]
  rfl

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The actual norm to base has rational degree equal to the original upper-field degree. -/
theorem ideleClassRationalDegree_normToBase (H : ClosedSubgroup Gal(Ω/K))
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H) :=
      abstractFixedField_finiteDimensional K Ω H hfinite
    let _ := hfinite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H)),
      ideleClassRationalDegree k K Ω
          (normToBase (ideleClassRepresentation k K Ω) H
            (abstractFixedClassEquiv k K Ω H hfinite c)).1 =
        ((IdeleClassGroup.degree (k := k) (K := abstractFixedField K Ω H) c.toMul).toAdd : ℚ) := by
  intro hEfinite hQfinite c
  change ideleClassRationalDegree k K Ω
    (relativeNorm (ideleClassRepresentation k K Ω) (baseField Gal(Ω/K)) H (le_baseField H)
      (abstractFixedClassEquiv k K Ω H hfinite c)).1 = _
  rw [ideleClassRationalDegree_relativeNorm, ideleClassRationalDegree_abstractFixedClassEquiv,
    ← abstractFixedField_finrank_eq_card K Ω H, nsmul_eq_mul, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _
    (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := K) (M := abstractFixedField K Ω H)).ne')

end FunctionField
