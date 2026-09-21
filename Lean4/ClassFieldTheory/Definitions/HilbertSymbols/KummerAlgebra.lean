import Mathlib.FieldTheory.KummerExtension

set_option autoImplicit false

/-!
# Canonical Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra `K[X] / (X^n - a)`.  It remains canonical when the
polynomial is reducible, so no root in a chosen closure is required. -/
abbrev KummerAlgebra
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :=
  AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))

end ClassFieldTheory
