import LocalClassFieldTheory.Concrete.ClassFormation
import LocalClassFieldTheory.Concrete.Finite
import LocalClassFieldTheory.Concrete.Infinite
import LocalClassFieldTheory.Concrete.Kummer
import LocalClassFieldTheory.Concrete.LubinTateApplication

/-!
# Concrete local class field theory

Public aggregate for finite local reciprocity, the finite local existence
order isomorphism, the absolute local Artin map, the local Kummer pairing,
Lubin--Tate applications, and profinite local reciprocity.
Public declarations live in the `LocalClassFieldTheory` namespace; implementation
modules may depend on `ValuationTheory`,
`LocalFieldTheory`, `RamificationTheory`, `CyclicCohomology`, `KummerTheory`, and
`AbstractClassFieldTheory` (whose declarations use the `ClassFormation`
namespace), while remaining independent of development-only modules.
-/
