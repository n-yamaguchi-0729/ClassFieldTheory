/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGalois

/-!
# Finite Galois towers obtained by adjoining constants upstairs

Adjoining finite constants to a finite Galois intermediate field gives an
extension which is finite Galois over the original base as well. The supply
comes from the actual identity between the relative constant compositum and
the supremum of the original field and the constant extension of the base.
-/

noncomputable section

namespace FunctionField

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Finite k] (L : FiniteGaloisIntermediateField K Ω)
    (C : IntermediateField k Ω) [FiniteDimensional k C]

/-- A finite constant extension of a finite Galois intermediate field is
finite over the original base. -/
theorem finiteDimensional_constantExtension_over_base :
    FiniteDimensional K (IntermediateField.adjoin L (C : Set Ω)) := by
  have : FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) :=
    finiteDimensional_constantExtension_of_finite (K := K) C
  change FiniteDimensional K
    ((IntermediateField.adjoin L (C : Set Ω)).restrictScalars K)
  rw [IntermediateField.restrictScalars_adjoin_eq_sup]
  infer_instance

/-- The relative constant compositum remains Galois over the original base:
it is the compositum of two Galois extensions of that base. -/
theorem isGalois_constantExtension_over_base :
    IsGalois K (IntermediateField.adjoin L (C : Set Ω)) := by
  have : IsGalois K (IntermediateField.adjoin K (C : Set Ω)) :=
    isGalois_constantExtension (K := K) C
  change IsGalois K
    ((IntermediateField.adjoin L (C : Set Ω)).restrictScalars K)
  rw [IntermediateField.restrictScalars_adjoin_eq_sup]
  infer_instance

end FunctionField
