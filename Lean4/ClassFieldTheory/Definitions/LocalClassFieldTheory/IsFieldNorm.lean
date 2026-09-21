import ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup

set_option autoImplicit false

/-!
# Predicate for field norms
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A nonzero element of `K` is a field norm from `L`. -/
def IsFieldNorm
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Prop :=
  x ∈ fieldNormSubgroup K L

end ClassFieldTheory
