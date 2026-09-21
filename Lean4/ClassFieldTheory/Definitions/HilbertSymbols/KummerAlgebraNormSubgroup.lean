import ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Mathlib.RingTheory.Norm.Basic

set_option autoImplicit false

/-!
# Norm subgroup of a Kummer algebra

This is the image of the determinant norm on units of `K[X] / (X^n - a)`.
The algebra need not be a field, so this subgroup is defined without any
irreducibility assumption on the polynomial.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- The unit-norm image of the possibly reducible Kummer algebra. -/
def kummerAlgebraNormSubgroup
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : KummerAlgebra K n a →* K)).range

end ClassFieldTheory
