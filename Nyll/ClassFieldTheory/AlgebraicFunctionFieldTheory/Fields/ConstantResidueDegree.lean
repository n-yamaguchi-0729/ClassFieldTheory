/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantRestrictionFixedField
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField

/-!
# Abstract residue degree is the actual constant-field degree

The image index of the absolute constant degree is computed by Galois
correspondence on the constant closure. Restriction of scalars then gives
the full constant-field factor relative to the original finite base.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- The abstract residue degree is the degree of the actual constants over
those of the original function field. -/
theorem residueDegree_eq_finrank_fullConstants (H : FiniteAbstractField Gal(Ω/K)) :
    (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) =
      Module.finrank (algebraicClosure k K)
        (algebraicClosure (algebraicClosure k K) (abstractFixedField K Ω H.field)) := by
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have hc : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hi := (fullConstantDegreeData k K Ω).fieldImageAdd_index
    (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω))
  change ((fullConstantDegreeData k K Ω).fieldImage H.field).index =
    (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) at hi
  rw [DegreeData.fieldImage_eq_map] at hi
  exact hi.symm.trans
    (finrank_constants_eq_absoluteConstantDegree_index (algebraicClosure k K) K Ω H.field).symm

variable [Algebra k Ω] [IsScalarTower k K Ω]

/-- Over the original constants, the actual constant degree is multiplied
by precisely the abstract residue degree. -/
theorem fullConstants_finrank_eq_mul_residueDegree (H : FiniteAbstractField Gal(Ω/K)) :
    Module.finrank k (algebraicClosure k (abstractFixedField K Ω H.field)) =
      Module.finrank k (algebraicClosure k K) *
        (H.residueDegree (fullConstantDegreeData k K Ω) : ℕ) := by
  let c := algebraicClosure k K
  let E := abstractFixedField K Ω H.field
  have hkCE : IsScalarTower k c E :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
  have hclosure : algebraicClosure k E = (algebraicClosure c E).restrictScalars k :=
    algebraicClosure.eq_restrictScalars_of_isAlgebraic k c E
  rw [residueDegree_eq_finrank_fullConstants]
  calc
    Module.finrank k (algebraicClosure k E) =
        Module.finrank k ((algebraicClosure c E).restrictScalars k) :=
      (IntermediateField.equivOfEq hclosure).toLinearEquiv.finrank_eq
    _ = Module.finrank k c * Module.finrank c (algebraicClosure c E) :=
      (Module.finrank_mul_finrank k c (algebraicClosure c E)).symm

end FunctionField
