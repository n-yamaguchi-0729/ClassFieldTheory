import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup.Basic

set_option autoImplicit false

/-!
# Fractional-ideal group of a number field
-/

open scoped NumberField
open NumberField

namespace ClassFieldTheory

universe u

/-- The group of nonzero fractional ideals of a number field. -/
abbrev NumberFieldFractionalIdealGroup
    (K : Type u) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

end ClassFieldTheory
