import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization

set_option autoImplicit false

/-!
# Equal-characteristic Laurent model for Lubin--Tate theory

Public aggregate for the reusable Laurent-series model and its normalized
uniformizer.  Transport of the exact norm-subgroup calculation to an arbitrary
equal-characteristic local field uses finite local reciprocity and is exported
by `LocalClassFieldTheory.LubinTateApplication`.
-/
