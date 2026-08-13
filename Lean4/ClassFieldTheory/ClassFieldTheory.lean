import ValuationTheory
import LocalFieldTheory
import RamificationTheory
import LubinTate
import CyclicCohomology
import KummerTheory
import AbstractClassFieldTheory
import AlgebraicNumberTheory
import LocalClassFieldTheory
import KroneckerWeber
import HasseArf
import GlobalClassFieldTheory

/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory, so downstream
users acquire exactly the maintained production declarations.

The library contains local class field theory and global class field theory
for number fields, together with the Hasse--Arf and Kronecker--Weber
theorems. Shared valuation, ramification, cohomology, Kummer, local-field,
and Lubin--Tate infrastructure lives beside those theories rather than under
a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.
-/
