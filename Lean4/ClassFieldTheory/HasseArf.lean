import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.Filtered
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.Filtered.FiniteAbelian
import RamificationTheory.LocalField

/-!
# Hasse--Arf

Reader-facing facade for the Hasse--Arf theorem: upper ramification jumps of
finite Abelian local extensions are integral.  Reusable ramification,
Lubin--Tate, and local reciprocity infrastructure is exported by its owner
libraries rather than through this facade.
-/

/-!
# Hasse--Arf integrality

Filtered local reciprocity identifies the Artin principal-unit step
filtration with the upper ramification filtration.  Since the former changes
only at natural-number indices, every upper jump of a finite Abelian local
extension is integral (with the separate possible endpoint `-1`).
-/

noncomputable section

namespace HasseArf

open LocalClassFieldTheory
open RamificationTheory
open RamificationTheory.LocalField

/-! ## From filtered reciprocity to integral upper jumps -/

/-- If filtered local reciprocity has been established for a finite Abelian
extension at nonnegative indices, then the right-limit at a nonnegative
index is the right-limit of the Artin principal-unit filtration. -/
theorem
    localUpperRamificationGroupAfter_eq_artinPrincipalUnitStepGroupAfter_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    (t : ℝ) (ht : 0 ≤ t) :
    localUpperRamificationGroupAfter K L t =
      natCeilStepFiltrationAfter (artinPrincipalUnitGroup K L) t := by
  unfold localUpperRamificationGroupAfter
  unfold natCeilStepFiltrationAfter
  apply iSup_congr
  intro s
  exact (hfiltered s (ht.trans s.property.le)).symm

/-- At a nonnegative index, filtered local reciprocity identifies intrinsic
upper jumps with jumps of the Artin principal-unit step filtration. -/
theorem
    isLocalUpperRamificationJump_iff_isArtinPrincipalUnitJump_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    (t : ℝ) (ht : 0 ≤ t) :
    IsLocalUpperRamificationJump K L t ↔
      IsArtinPrincipalUnitJump K L t := by
  unfold IsLocalUpperRamificationJump
  unfold IsArtinPrincipalUnitJump
  rw [← hfiltered t ht]
  rw [
    localUpperRamificationGroupAfter_eq_artinPrincipalUnitStepGroupAfter_of_filteredLocalReciprocity
      K L hfiltered t ht]
  rfl

/-- The nonnegative part of the formal Hasse--Arf implication: once filtered
local reciprocity is known for a finite Abelian extension, every nonnegative
actual upper jump is a natural number.  The possible index `-1` is handled
separately from the principal-unit filtration. -/
theorem
    isLocalUpperRamificationJump_integer_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    {t : ℝ} (ht0 : 0 ≤ t)
    (ht : IsLocalUpperRamificationJump K L t) :
    ∃ n : ℕ, t = n := by
  exact isArtinPrincipalUnitJump_integer K L
    ((isLocalUpperRamificationJump_iff_isArtinPrincipalUnitJump_of_filteredLocalReciprocity
      K L hfiltered t ht0).mp ht)

/-- The full formal Hasse--Arf implication from filtered local reciprocity:
every actual upper jump is an integer.  The endpoint `-1` is treated directly,
while every other jump is nonnegative and hence comes from the natural-number
principal-unit filtration. -/
theorem
    isLocalUpperRamificationJump_int_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    {t : ℝ} (ht : IsLocalUpperRamificationJump K L t) :
    ∃ z : ℤ, t = z := by
  rcases isLocalUpperRamificationJump_eq_neg_one_or_nonneg K L ht with hneg | ht0
  · exact ⟨-1, by simpa using hneg⟩
  · obtain ⟨n, hn⟩ :=
      isLocalUpperRamificationJump_integer_of_filteredLocalReciprocity
        K L hfiltered ht0 ht
    exact ⟨n, by simpa using hn⟩

/-- Hasse--Arf integrality: every actual upper ramification jump of
a finite Abelian local extension is an integer. -/
theorem isLocalUpperRamificationJump_int
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {t : ℝ} (ht : IsLocalUpperRamificationJump K L t) :
    ∃ z : ℤ, t = z := by
  exact
    isLocalUpperRamificationJump_int_of_filteredLocalReciprocity
      K L
      (fun s hs =>
        finiteAbelian_filteredLocalReciprocity K L s hs)
      ht

end HasseArf
