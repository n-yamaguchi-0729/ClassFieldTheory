import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport

/-!
# Reusable Lubin--Tate norm calculations in equal characteristic

Public aggregate for higher-unit norms, containment of the standard subgroup
in the finite-level norm subgroup, and the corresponding finite quotient
calculation.  The exact norm-subgroup equality, which uses finite local
reciprocity, is exported by
`LocalClassFieldTheory.Concrete.LubinTateApplication`.
-/
