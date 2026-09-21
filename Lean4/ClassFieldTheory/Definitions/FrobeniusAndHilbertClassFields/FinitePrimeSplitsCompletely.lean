import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option autoImplicit false

/-!
# Complete splitting of a finite prime
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A finite prime splits completely when every prime above it has
ramification index and inertia degree equal to one. -/
def FinitePrimeSplitsCompletely
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L),
    w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
      w.asIdeal.inertiaDeg (𝓞 K) = 1

end ClassFieldTheory
