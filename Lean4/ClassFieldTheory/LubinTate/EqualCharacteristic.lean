import LubinTate.EqualCharacteristic.CompletedLevel
import LubinTate.EqualCharacteristic.Existence
import LubinTate.EqualCharacteristic.FiniteLevel
import LubinTate.EqualCharacteristic.FormalModule
import LubinTate.EqualCharacteristic.Frobenius
import LubinTate.EqualCharacteristic.NormSubgroup
import LubinTate.EqualCharacteristic.Theta
import LubinTate.EqualCharacteristic.RealIndexSteps
import LubinTate.EqualCharacteristic.Ramification

/-!
# Equal-characteristic Lubin--Tate theory

Public aggregate for the equal-characteristic Lubin--Tate construction.  It
includes the Laurent-series model, finite and completed Lubin--Tate levels,
and the Frobenius and theta constructions.  The local-class-field-theory
norm-subgroup calculation and its transport live in
`LocalClassFieldTheory.Concrete.LubinTateApplication`.

Each mathematical stage has a reader-facing aggregate below
`LubinTate.EqualCharacteristic`; declarations remain in the matching
namespace.
-/
