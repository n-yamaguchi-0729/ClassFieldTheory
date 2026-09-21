import Mathlib.RingTheory.Norm.Basic

set_option autoImplicit false

/-!
# The field norm on multiplicative groups
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The field norm as a homomorphism on multiplicative groups. -/
def fieldNormHom
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

end ClassFieldTheory
