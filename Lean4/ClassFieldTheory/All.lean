import ClassFieldTheory.AbstractClassFieldTheory.All
import ClassFieldTheory.AlgebraicNumberTheory.All
import ClassFieldTheory.GlobalClassFieldTheory.All
import ClassFieldTheory.HasseArf
import ClassFieldTheory.KroneckerWeber.All
import ClassFieldTheory.KummerTheory.All
import ClassFieldTheory.LocalClassFieldTheory.All
import ClassFieldTheory.LocalFieldTheory.All
import ClassFieldTheory.LubinTate.All
import ClassFieldTheory.RamificationTheory.All

set_option autoImplicit false

/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory.  Compile-time
API, instance-coherence, and normal-form checks live behind the independent
`ClassFieldTheoryTests` target, so downstream users do not acquire test-only work.

The library contains local class field theory and global class field theory
for number fields, including the Hilbert product formula, general
power-residue reciprocity, and Gauss quadratic reciprocity, together with the
Hasse--Arf and Kronecker--Weber theorems. Shared valuation, ramification,
cohomology, Kummer, local-field, and Lubin--Tate infrastructure lives beside
those theories rather than under a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.  Maintainers can compile `ClassFieldTheoryTests`
separately to verify every supported import surface without changing the public root.
-/
