/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.BaseDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantResidueDegree

/-!
# The actual function-field valuation datum

Normalized idele degree supplies the integer-valued henselian valuation for
the actual absolute idele-class representation and constant-field degree.
The norm-image axiom follows from the proved abstract norm degree formula,
the actual constant-field index, and surjectivity of normalized degree.
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

/-- The actual normalized degree of an abstract norm is multiplied by the
actual constant residue degree. -/
theorem ideleClassBaseIntegerDegree_norm (H : FiniteAbstractField Gal(Ω/K)) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H.field)),
      ideleClassBaseIntegerDegree k K Ω
          (normToBase (ideleClassRepresentation k K Ω) H.field
            (abstractFixedClassEquiv k K Ω H.field H.finite c)) =
        (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) *
          (IdeleClassGroup.normalizedDegree (k := k)
            (K := abstractFixedField K Ω H.field) c.toMul).toAdd := by
  intro hE c
  apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr (fullConstants_degree_pos k K).ne')
  calc
    (Module.finrank k (algebraicClosure k K) : ℤ) * _ =
        (IdeleClassGroup.degree (k := k) (K := abstractFixedField K Ω H.field) c.toMul).toAdd :=
      fullConstants_mul_ideleClassBaseIntegerDegree_norm k K Ω H c
    _ = (Module.finrank k (algebraicClosure k (abstractFixedField K Ω H.field)) : ℤ) *
        (IdeleClassGroup.normalizedDegree (k := k)
          (K := abstractFixedField K Ω H.field) c.toMul).toAdd :=
      (IdeleClassGroup.fullConstants_mul_normalizedDegree c.toMul).symm
    _ = _ := by rw [fullConstants_finrank_eq_mul_residueDegree, Nat.cast_mul, mul_assoc]

/-- The values of all actual abstract norms form exactly the residue-degree
multiple of the integer value group. -/
theorem ideleClassBaseDegree_norm_range (H : FiniteAbstractField Gal(Ω/K)) :
    ((ideleClassBaseDegree k K Ω).comp
      (normToBase (ideleClassRepresentation k K Ω) H.field)).range =
        nsmulImage (ideleClassBaseDegree k K Ω).range
          (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) := by
  have hE : FiniteDimensional K (abstractFixedField K Ω H.field) :=
    abstractFixedField_finiteDimensional K Ω H.field H.finite
  rw [ideleClassBaseDegree_range]
  apply AddSubgroup.ext
  intro z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := (abstractFixedClassEquiv k K Ω H.field H.finite).surjective a
    let n : ℤ := (IdeleClassGroup.normalizedDegree (k := k)
      (K := abstractFixedField K Ω H.field) c.toMul).toAdd
    refine ⟨(n : ZHat), ⟨n, rfl⟩, ?_⟩
    change (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) • (n : ZHat) =
      (ideleClassBaseIntegerDegree k K Ω
      (normToBase (ideleClassRepresentation k K Ω) H.field
        (abstractFixedClassEquiv k K Ω H.field H.finite c)) : ZHat)
    rw [ideleClassBaseIntegerDegree_norm, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  · rintro ⟨w, ⟨n, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := IdeleClassGroup.normalizedDegree_surjective
      (k := k) (K := abstractFixedField K Ω H.field) (Multiplicative.ofAdd n)
    refine ⟨abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c), ?_⟩
    change (ideleClassBaseIntegerDegree k K Ω
      (normToBase (ideleClassRepresentation k K Ω) H.field
        (abstractFixedClassEquiv k K Ω H.field H.finite (Additive.ofMul c))) : ZHat) = _
    rw [ideleClassBaseIntegerDegree_norm]
    change ((((H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) : ℤ) *
      (IdeleClassGroup.normalizedDegree (k := k)
        (K := abstractFixedField K Ω H.field) c).toAdd : ℤ) : ZHat) =
          (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) • (n : ZHat)
    rw [hc, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
    rfl

/-- The concrete henselian valuation for function-field class formation. -/
def ideleClassValuationData :
    ValuationData (fullConstantDegreeData k K Ω) (ideleClassRepresentation k K Ω) where
  toAddMonoidHom := ideleClassBaseDegree k K Ω
  integers_mem n := by
    rw [ideleClassBaseDegree_range]
    exact ⟨n, rfl⟩
  canonical_value_quotient_bijective := ideleClassBaseDegree_quotient_bijective k K Ω
  norm_range := ideleClassBaseDegree_norm_range k K Ω

end FunctionField
