import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

set_option autoImplicit false

/-!
# Unramifiedness at every place
-/

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified at all finite and infinite places. -/
def IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  IsUnramifiedAtFinitePlaces K L ∧ IsUnramifiedAtInfinitePlaces K L

end ClassFieldTheory
