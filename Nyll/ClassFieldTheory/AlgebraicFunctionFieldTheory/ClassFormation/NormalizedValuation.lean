/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Valuation

/-!
# Normalized valuation on each actual fixed field

The abstract valuation at a finite field is the ordinary normalized degree
of its actual idele classes. The residue-degree norm identity and injectivity
of multiplication on the profinite integers give the comparison.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- At every finite fixed field, the abstract valuation is its actual normalized idele degree. -/
theorem ideleClassValuationData_valuationAt (H : FiniteAbstractField Gal(Ω/K)) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H.field),
      ((ideleClassValuationData k K Ω).valuationAt H
        (abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c)) : ZHat) =
      ((IdeleClassGroup.normalizedDegree (k := k)
        (K := abstractFixedField K Ω H.field) c).toAdd : ZHat) := by
  intro hFfinite c
  let v := ideleClassValuationData k K Ω
  let a := abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c)
  apply zHatMulNat_injective (H.residueDegree (fullConstantDegreeData k K Ω)).property
  change (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) • v.dividedAt H a = _
  rw [v.residueDegree_nsmul_dividedAt]
  change (ideleClassBaseIntegerDegree k K Ω
      (normToBase (ideleClassRepresentation k K Ω) H.field a) : ZHat) =
    (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) •
      ((IdeleClassGroup.normalizedDegree (k := k)
        (K := abstractFixedField K Ω H.field) c).toAdd : ZHat)
  rw [ideleClassBaseIntegerDegree_norm, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  rfl

end FunctionField
