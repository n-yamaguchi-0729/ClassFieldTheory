import ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# The field-norm quotient
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The norm quotient `Kˣ / N_{L/K}(Lˣ)`. -/
abbrev FieldNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :=
  Kˣ ⧸ fieldNormSubgroup K L

end ClassFieldTheory
