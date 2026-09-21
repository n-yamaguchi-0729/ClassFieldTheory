import ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Mathlib.RingTheory.Norm.Basic

set_option autoImplicit false

/-!
# Norms from Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- A nonzero element `b` is a norm from the Kummer algebra
`K[X] / (X^n - a)`. -/
def IsKummerNorm
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) : Prop :=
  ∃ y : (KummerAlgebra K n a)ˣ,
    Algebra.norm K (y : KummerAlgebra K n a) = (b : K)

end ClassFieldTheory
