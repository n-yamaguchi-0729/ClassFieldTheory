/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFiltered
public import Nyll.ValuedFieldTheory.Ramification.LocalField.FirstRamificationComparison
public import Nyll.ValuedFieldTheory.Ramification.LocalField.InertiaCard
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure

/-!
# The actual tame conductor criterion in independent field universes

The specified Artin map identifies principal-unit images with the original chosen upper
ramification groups. At depth one this gives the conductor threshold through the actual
Hilbert ramification group and the original valued-extension ramification index.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory RamificationTheory.LocalField
open scoped ValuativeRel

/-- The actual principal-unit image vanishes precisely from the original norm conductor onward. -/
theorem artinPrincipalUnitGroup_eq_bot_iff
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] (n : ℕ) :
    artinPrincipalUnitGroup K L n = ⊥ ↔ localConductorExponent K L ≤ n := by
  rw [artinPrincipalUnitGroup, Subgroup.map_eq_bot_iff,
    abelianLocalArtinMonoidHom_ker, localConductorExponent_le_iff]

/-- In a finite abelian local extension the first upper and lower groups
coincide. The normalization matters: `φ(1)` need not equal `1`, but it lies
in `(0, 1]`, where filtered reciprocity makes the upper group constant. -/
theorem finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localUpperRamificationGroup K L 1 =
      localLowerRamificationGroup K L 1 := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let s : ℝ :=
    RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq 1
  have hs : 0 < s ∧ s ≤ 1 := by
    change (open _root_.RamificationTheory.DiscreteValuationField in
      open _root_.RamificationTheory.HilbertRamification.Higher in
      0 < (AntitoneNormalSubgroupFiltration.herbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq)) 1 ∧
        (AntitoneNormalSubgroupFiltration.herbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq)) 1 ≤ 1)
    exact (open _root_.RamificationTheory.DiscreteValuationField in
      AntitoneNormalSubgroupFiltration.herbrandFunction_one_pos_le_one _)
  have hStep (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      localUpperRamificationGroup K L t =
        artinPrincipalUnitGroup K L 1 := by
    have hceil : ⌈t⌉₊ = 1 :=
      (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).2
        (by simpa only [Nat.sub_self, Nat.cast_zero, Nat.cast_one] using
          (show (0 : ℝ) < t ∧ t ≤ 1 from ⟨ht0, ht1⟩))
    calc
      localUpperRamificationGroup K L t =
          artinPrincipalUnitStepGroup K L t :=
        (finiteAbelian_filteredLocalReciprocity K L t ht0.le).symm
      _ = artinPrincipalUnitGroup K L 1 := by
        change artinPrincipalUnitGroup K L ⌈t⌉₊ = _
        rw [hceil]
  have hAtS :
      localUpperRamificationGroup K L s =
        localLowerRamificationGroup K L 1 := by
    change RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
        (base := base) (target := target) huniq
        (RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq 1) =
      RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
        (base := base) (target := target) huniq 1
    exact (open _root_.RamificationTheory.HilbertRamification.Higher in
      upperRamificationGroupOfUniqueExtension_herbrandFunction
        (base := base) (target := target) huniq 1)
  calc
    localUpperRamificationGroup K L 1 = artinPrincipalUnitGroup K L 1 :=
      hStep 1 (by norm_num) le_rfl
    _ = localUpperRamificationGroup K L s := (hStep s hs.1 hs.2).symm
    _ = localLowerRamificationGroup K L 1 := hAtS

/-- The first upper group of a finite abelian local extension is Hilbert's
ramification group for the chosen valuation ring, transported to `Gal(L/K)`. -/
theorem finiteAbelian_localUpperRamificationGroup_one_eq_hilbertRamificationGroup
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localUpperRamificationGroup K L 1 =
      Subgroup.comap
        (RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup
          (base := localCompleteDVF K)
          (target := chosenLocalExtensionCompleteDVF K L)).toMonoidHom
        (RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInDecomposition K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring) :=
  (finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one K L).trans
    (localLowerRamificationGroup_one_eq_hilbertRamificationGroup K L)

/-- For a finite abelian local extension, the conductor exponent is at most
one exactly when its first upper ramification group is trivial.  This is the
filtered-reciprocity bridge used by the tame-ramification criterion. -/
theorem localConductorExponent_le_one_iff_localUpperRamificationGroup_one_eq_bot
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localConductorExponent K L ≤ 1 ↔
      localUpperRamificationGroup K L 1 = ⊥ := by
  have hstep :
      artinPrincipalUnitStepGroup K L (1 : ℝ) =
        artinPrincipalUnitGroup K L 1 := by
    change artinPrincipalUnitGroup K L ⌈(1 : ℝ)⌉₊ =
      artinPrincipalUnitGroup K L 1
    have hone : ⌈(1 : ℝ)⌉₊ = (1 : ℕ) := by norm_num
    rw [hone]
  rw [← finiteAbelian_filteredLocalReciprocity K L 1 (by norm_num), hstep]
  exact (artinPrincipalUnitGroup_eq_bot_iff K L 1).symm

/-- Conductor exponent at most one is equivalent to the absence of wild
ramification in the chosen valuation ring. -/
theorem localConductorExponent_le_one_iff_hilbertRamificationGroup_eq_bot
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localConductorExponent K L ≤ 1 ↔
      RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring = ⊥ := by
  rw [localConductorExponent_le_one_iff_localUpperRamificationGroup_one_eq_bot,
    finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one]
  exact localLowerRamificationGroup_one_eq_bot_iff_hilbertRamificationGroup_eq_bot K L

/-- The first conductor threshold is the usual tame criterion: the residue
characteristic does not divide the ramification index. -/
theorem localConductorExponent_le_one_iff_residueChar_not_dvd_ramificationIndex
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring) p] :
    localConductorExponent K L ≤ 1 ↔
      ¬ p ∣ ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        (localCompleteDVF K).toDVF
        (chosenLocalExtensionCompleteDVF K L).toDVF := by
  let A := (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
  rw [localConductorExponent_le_one_iff_hilbertRamificationGroup_eq_bot]
  exact (open _root_.RamificationTheory.HilbertRamification.ValuationSubring in
    ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card K A p).trans (by
      rw [RamificationTheory.LocalField.chosenLocalExtension_inertia_card_eq_ramificationIndex K L])

end LocalClassFieldTheory.Universe
