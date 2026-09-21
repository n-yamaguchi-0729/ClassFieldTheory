import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

/-!
# Open finite-index subgroups of a field's multiplicative group
-/

namespace ClassFieldTheory

universe u

/-- An open finite-index subgroup of the multiplicative group `Kˣ`.  The
inherited order is ordinary subgroup inclusion. -/
abbrev OpenFiniteIndexSubgroup
    (K : Type u) [Field K] [TopologicalSpace K] :=
  { H : Subgroup Kˣ // IsOpen (H : Set Kˣ) ∧ H.FiniteIndex }

end ClassFieldTheory
