import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

set_option autoImplicit false

/-!
# Existence of the small Hilbert class field

The small Hilbert class field is characterized as an everywhere-unramified
finite abelian extension containing every other such extension.  In
particular, real places are required to remain unramified.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal everywhere-unramified finite abelian extension exists. -/
theorem exists_smallHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsSmallHilbertClassField E :=
  GlobalClassFieldComparison.exists_smallHilbertClassField K

end ClassFieldTheory
