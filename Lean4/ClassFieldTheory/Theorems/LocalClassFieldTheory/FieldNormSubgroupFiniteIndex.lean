import ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface

set_option autoImplicit false

/-!
# Finite index of the local norm subgroup

Finite local reciprocity implies that the subgroup of nonzero field norms
has finite index in the multiplicative group of the base field.
-/

namespace ClassFieldTheory

/-- The norm subgroup of a finite abelian local extension has finite index. -/
theorem fieldNormSubgroup_finiteIndex
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).FiniteIndex := by
  exact LocalCFT.fieldNormSubgroup_finiteIndex K L

end ClassFieldTheory
