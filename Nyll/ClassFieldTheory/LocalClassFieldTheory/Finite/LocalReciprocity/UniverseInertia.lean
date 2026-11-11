/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkResidueTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Filtration
public import Nyll.ValuedFieldTheory.Ramification.LocalField.ResidueInertia

/-!
# Actual unit images and residue inertia in independent universes

The same field equivalences used to define the Artin map identify the actual integer units.
Their restrictions identify the actual inertia kernels by the difference-in-maximal-ideal
criterion. Native filtered reciprocity is used only at depth zero on these small fields.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

universe u v

/-- The specified Artin map sends integral units onto the actual residue-action kernel. -/
theorem abelianLocalArtinMonoidHom_units_eq_residue_ker
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (fieldPrincipalUnits K 0).map (abelianLocalArtinMonoidHom K L) =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  let : Small.{0} K := smallLocalField K
  let : Small.{0} L := smallLocalField L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_isAbelianGalois K L
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  let : IsNonarchimedeanLocalField (Shrink.{0} L) :=
    shrinkLocalField_isNonarchimedeanLocalField L
  let : Valuation.HasExtension
      (ValuativeRel.valuation (Shrink.{0} K)) (ValuativeRel.valuation (Shrink.{0} L)) :=
    shrink_valuationHasExtension K L
  let : IsIntegralClosure 𝒪[Shrink.{0} L] 𝒪[Shrink.{0} K] (Shrink.{0} L) :=
    localCompleteDVF_integerRing_isIntegralClosure (Shrink.{0} K) (Shrink.{0} L)
  let : Module.Finite 𝒪[Shrink.{0} K] 𝒪[Shrink.{0} L] :=
    localCompleteDVF_integerRing_moduleFinite (Shrink.{0} K) (Shrink.{0} L)
  let eU := shrinkUnitsContinuousMulEquiv K
  let eG := HasseArf.shrinkGalMulEquiv K L
  let eK := shrinkIntegerRingEquiv K
  let eL := shrinkIntegerRingEquiv L
  have hunit (a : (Shrink.{0} K)ˣ) :
      eU a ∈ fieldPrincipalUnits K 0 ↔ a ∈ fieldPrincipalUnits (Shrink.{0} K) 0 := by
    change eU a ∈ (principalUnits K 0).map (integerUnitsToFieldUnits K) ↔
      a ∈ (principalUnits (Shrink.{0} K) 0).map (integerUnitsToFieldUnits (Shrink.{0} K))
    rw [principalUnits_zero, principalUnits_zero]
    constructor
    · intro h
      rcases Subgroup.mem_map.mp h with ⟨b, _hb, hba⟩
      obtain ⟨b₀, rfl⟩ := (Units.mapEquiv eK.toMulEquiv).surjective b
      refine Subgroup.mem_map.mpr ⟨b₀, Subgroup.mem_top _, ?_⟩
      apply eU.injective
      exact (shrinkIntegerUnitsToFieldUnits K b₀).trans hba
    · intro h
      rcases Subgroup.mem_map.mp h with ⟨b, _hb, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Units.mapEquiv eK.toMulEquiv b,
        Subgroup.mem_top _, (shrinkIntegerUnitsToFieldUnits K b).symm⟩
  have hArtin (a : (Shrink.{0} K)ˣ) :
      abelianLocalArtinMonoidHom K L (eU a) =
        eG (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (Shrink.{0} K) (Shrink.{0} L) a) := by
    rw [← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom]
    apply AlgEquiv.ext
    intro z
    obtain ⟨z₀, rfl⟩ := (Shrink.ringEquiv L).surjective z
    change abelianLocalArtinMap K L (eU a) (Shrink.ringEquiv L z₀) =
      HasseArf.shrinkGalEquiv K L
        (_root_.LocalClassFieldTheory.abelianLocalArtinMap
          (Shrink.{0} K) (Shrink.{0} L) a) (Shrink.ringEquiv L z₀)
    rw [abelianLocalArtinMap_apply_shrink, ContinuousMulEquiv.symm_apply_apply,
      HasseArf.shrinkGalEquiv_apply]
  have hmax (a : 𝒪[Shrink.{0} L]) :
      eL a ∈ (𝓂[L] : Ideal 𝒪[L]) ↔
        a ∈ (𝓂[Shrink.{0} L] : Ideal 𝒪[Shrink.{0} L]) := by
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff eL,
      ← IsLocalRing.mem_maximalIdeal]
  have hker (σ : Gal(Shrink.{0} L / Shrink.{0} K)) :
      eG σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
        σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure
          (Shrink.{0} K) (Shrink.{0} L)).ker := by
    have hdelta (a : 𝒪[Shrink.{0} L]) :
        eL (galoisGroupIntegerRingEquivOfIsIntegralClosure
          (Shrink.{0} K) (Shrink.{0} L) σ a - a) =
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L (eG σ) (eL a) - eL a := by
      apply Subtype.ext
      change Shrink.ringEquiv L (σ (a : Shrink.{0} L) - (a : Shrink.{0} L)) =
        HasseArf.shrinkGalEquiv K L σ (Shrink.ringEquiv L (a : Shrink.{0} L)) -
          Shrink.ringEquiv L (a : Shrink.{0} L)
      rw [map_sub, HasseArf.shrinkGalEquiv_apply]
    rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal,
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
    constructor
    · intro h a
      apply (hmax _).mp
      rw [hdelta]
      exact h (eL a)
    · intro h a
      obtain ⟨a₀, rfl⟩ := eL.surjective a
      rw [← hdelta, hmax]
      exact h a₀
  have hsmall :
      (fieldPrincipalUnits (Shrink.{0} K) 0).map
          (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom
            (Shrink.{0} K) (Shrink.{0} L)) =
        (galoisGroupResidueAlgEquivHomOfIsIntegralClosure
          (Shrink.{0} K) (Shrink.{0} L)).ker := by
    have h := _root_.LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity
      (Shrink.{0} K) (Shrink.{0} L) 0 le_rfl
    rw [RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker] at h
    simpa only [_root_.LocalClassFieldTheory.artinPrincipalUnitStepGroup_eq_nativeArtinImage,
      Nat.ceil_zero] using h
  apply Subgroup.ext
  intro σ
  obtain ⟨σ₀, rfl⟩ := eG.surjective σ
  rw [hker, ← hsmall]
  constructor
  · intro h
    rcases Subgroup.mem_map.mp h with ⟨a, ha, hσ⟩
    obtain ⟨a₀, rfl⟩ := eU.surjective a
    refine Subgroup.mem_map.mpr ⟨a₀, (hunit a₀).mp ha, ?_⟩
    apply eG.injective
    exact (hArtin a₀).symm.trans hσ
  · intro h
    rcases Subgroup.mem_map.mp h with ⟨a, ha, hσ⟩
    exact Subgroup.mem_map.mpr ⟨eU a, (hunit a).mpr ha,
      (hArtin a).trans (congrArg eG hσ)⟩

end LocalClassFieldTheory.Universe
