import ClassFieldTheory.LubinTate.EqualCharacteristic.All
import ClassFieldTheory.LubinTate.FiniteLevel.All
import ClassFieldTheory.LubinTate.FormalModule.All
import ClassFieldTheory.LubinTate.Padic.All

set_option autoImplicit false

/-!
# Lubin--Tate theory

This is the public aggregate for Lubin--Tate theory.  It exports the formal
module foundations, the characteristic-independent standard finite-level
division fields and their lower/upper ramification formulas, and the explicit
equal-characteristic construction.  The
norm-subgroup calculation and transport used by local class field theory are
exported from `LocalClassFieldTheory.LubinTateApplication`, and the
field-facing existence theorem from
`LocalClassFieldTheory.Finite.Existence.EqualCharacteristic`.
The equal-characteristic construction is organized by its mathematical stages
below `LubinTate.EqualCharacteristic`.
-/
