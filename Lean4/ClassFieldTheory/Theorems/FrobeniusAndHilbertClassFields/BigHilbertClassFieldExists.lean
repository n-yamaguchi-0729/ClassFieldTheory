import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

set_option autoImplicit false

/-!
# Existence of the big Hilbert class field

The big Hilbert class field is characterized intrinsically as a finite
abelian extension unramified at every finite prime and containing every
other finite abelian extension with that property.  No particular field
chosen by the implementation appears in the statement.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal finite-prime-unramified finite abelian extension exists. -/
theorem exists_bigHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsBigHilbertClassField E :=
  GlobalClassFieldComparison.exists_bigHilbertClassField K

end ClassFieldTheory
