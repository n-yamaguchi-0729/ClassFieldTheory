import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Multiplicative power-class groups
-/

namespace ClassFieldTheory

universe u

/-- The multiplicative group of a field modulo its `n`-th powers. -/
def PowerClassGroup (K : Type u) [Field K] (n : ℕ+) : Type u :=
  Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

instance instCommGroupPowerClassGroup
    (K : Type u) [Field K] (n : ℕ+) : CommGroup (PowerClassGroup K n) := by
  unfold PowerClassGroup
  infer_instance

end ClassFieldTheory
