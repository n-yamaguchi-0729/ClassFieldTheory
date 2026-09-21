import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

set_option autoImplicit false

/-!
# Small Hilbert class fields
-/

namespace ClassFieldTheory

universe u

/-- A small Hilbert class field is an everywhere-unramified finite abelian
extension containing every other such extension. -/
def IsSmallHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Prop :=
  IsEverywhereUnramified K E ∧
    ∀ F : FiniteAbelianExtension K,
      IsEverywhereUnramified K F → Nonempty (F →ₐ[K] E)

end ClassFieldTheory
