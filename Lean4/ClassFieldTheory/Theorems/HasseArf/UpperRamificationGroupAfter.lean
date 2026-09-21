import ClassFieldTheory.Definitions.HasseArf.IsUpperRamificationJump
import ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupAntitone

set_option autoImplicit false

/-!
# The right-limit upper ramification group
-/

namespace ClassFieldTheory

/-- The right-limit upper group lies in the group at the limiting index. -/
theorem upperRamificationGroupAfter_le
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    upperRamificationGroupAfter K L t ≤ upperRamificationGroup K L t := by
  apply iSup_le
  intro s
  exact upperRamificationGroup_antitone K L (le_of_lt s.property)

end ClassFieldTheory
