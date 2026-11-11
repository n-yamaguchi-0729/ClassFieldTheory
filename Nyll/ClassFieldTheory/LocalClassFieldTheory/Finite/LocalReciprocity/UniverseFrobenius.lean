/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseInertia
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedReciprocity
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkResidueTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius

/-!
# Frobenius normalization for the same Artin map in independent universes

The original valuations determine the small integer rings and their residue equivalences.
The existing maximal-ideal equality supplies unramifiedness of the small extension. Native local
reciprocity then gives the residue action on the original extension, with the same inverse-prime
normalization. No residue-action comparison is added as an assumption.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

universe u v

private theorem map_maximalIdeal_eq_of_commuting_ringEquivs
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (eR : R ≃+* R') (eS : S ≃+* S') {f : R →+* S} {g : R' →+* S'}
    (hcomm : eS.toRingHom.comp f = g.comp eR.toRingHom)
    (hmap : (IsLocalRing.maximalIdeal R').map g = IsLocalRing.maximalIdeal S') :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
  have hinv : f.comp eR.symm.toRingHom = eS.symm.toRingHom.comp g := by
    apply RingHom.ext
    intro x
    apply eS.injective
    change eS (f (eR.symm x)) = eS (eS.symm (g x))
    rw [eS.apply_symm_apply]
    have hx := DFunLike.congr_fun hcomm (eR.symm x)
    change eS (f (eR.symm x)) = g (eR (eR.symm x)) at hx
    rwa [eR.apply_symm_apply] at hx
  have hm := congrArg (Ideal.map eS.symm.toRingHom) hmap
  rw [Ideal.map_map, ← hinv, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective eR.symm.toRingHom eR.symm.surjective,
    IsLocalRing.map_maximalIdeal_of_surjective eS.symm.toRingHom eS.symm.surjective] at hm
  exact hm

private theorem ramificationIdx_eq_one_of_local_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R = 1 := by
  let q := IsLocalRing.maximalIdeal S
  let Sq := Localization.AtPrime q
  change q.ramificationIdx R = 1
  rw [Ideal.ramificationIdx_eq (IsLocalRing.maximalIdeal R) q, ENat.toNat_eq_iff_eq_natCast,
    Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, IsScalarTower.algebraMap_eq R S Sq, ← Ideal.map_map, hmap,
    Localization.AtPrime.map_eq_maximalIdeal]

section IndependentUniverses

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsUnramifiedValuedExtension K L]

/-- The same two small representatives form an unramified extension for the supplied valuations. -/
theorem shrink_isUnramifiedValuedExtension :
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
    IsUnramifiedValuedExtension (Shrink.{0} K) (Shrink.{0} L) := by
  intro sharedSmallK sharedSmallL sharedAlgebra sharedFinite sharedGalois sharedValuationK
    sharedValuationL sharedLocalK sharedLocalL sharedExtension
  let eK := shrinkIntegerRingEquiv K
  let eL := shrinkIntegerRingEquiv L
  have hcomm : eL.toRingHom.comp (algebraMap 𝒪[Shrink.{0} K] 𝒪[Shrink.{0} L]) =
      (algebraMap 𝒪[K] 𝒪[L]).comp eK.toRingHom := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    exact HasseArf.shrinkAlgebra_apply K L (x : Shrink.{0} K)
  have hmap := map_maximalIdeal_eq_of_commuting_ringEquivs eK eL hcomm
    (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation K L)
  exact ⟨ramificationIdx_eq_one_of_local_map hmap⟩

/-- The specified Artin map acts by arithmetic Frobenius on the actual residues of an unramified
extension. Value one is the inverse-DVR-uniformizer convention of the original native map. -/
theorem abelianLocalArtinMap_inverseUniformizer_residue_pow
    (π : Kˣ) (hπ : valuationMap K (Additive.ofMul π) = 1) (x : 𝒪[L]) :
    ∃ z : 𝒪[L],
      (z : L) = abelianLocalArtinMap K L π (x : L) ∧
        IsLocalRing.residue 𝒪[L] z = (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
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
  let : IsUnramifiedValuedExtension (Shrink.{0} K) (Shrink.{0} L) :=
    shrink_isUnramifiedValuedExtension K L
  let : UniformSpace (Shrink.{0} L) := IsTopologicalAddGroup.rightUniformSpace (Shrink.{0} L)
  let : IsUniformAddGroup (Shrink.{0} L) := isUniformAddGroup_of_addCommGroup
  let π₀ := (shrinkUnitsContinuousMulEquiv K).symm π
  have hπ₀ : valuationMap (Shrink.{0} K) (Additive.ofMul π₀) = 1 := by
    rw [← valuationMap_shrinkRingEquiv K π₀]
    change valuationMap K (Additive.ofMul
      (shrinkUnitsContinuousMulEquiv K ((shrinkUnitsContinuousMulEquiv K).symm π))) = 1
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact hπ
  let x₀ := (shrinkIntegerRingEquiv L).symm x
  obtain ⟨z₀, hz₀, hzres⟩ :=
    ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
      (Shrink.{0} K) (Shrink.{0} L) π₀ hπ₀ x₀
  refine ⟨shrinkIntegerRingEquiv L z₀, ?_, ?_⟩
  · rw [shrinkIntegerRingEquiv_coe, hz₀]
    have hx : Shrink.ringEquiv L (x₀ : Shrink.{0} L) = (x : L) :=
      congrArg (fun y : 𝒪[L] => (y : L)) ((shrinkIntegerRingEquiv L).apply_symm_apply x)
    rw [← abelianLocalArtinMap_apply_shrink K L π (x₀ : Shrink.{0} L), hx]
  · have h := congrArg (shrinkResidueFieldEquiv L) hzres
    rw [shrinkResidueFieldEquiv_residue, map_pow, shrinkResidueFieldEquiv_residue,
      (shrinkIntegerRingEquiv L).apply_symm_apply, shrinkResidueField_card K] at h
    exact h

end IndependentUniverses

section ActualFrobenius

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsUnramifiedValuedExtension K L]

/-- In independent field universes, the specified Artin value is the actual field
Frobenius, as determined by its action on the actual residue field. -/
theorem abelianLocalArtinMap_uniformizer
    (π : Kˣ) (hπ : valuationMap K (Additive.ofMul π) = 1) :
    abelianLocalArtinMap K L π = arithmeticFrobeniusOfUnramifiedValuation K L := by
  apply galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨z, hz, hres⟩ := abelianLocalArtinMap_inverseUniformizer_residue_pow K L π hπ x
  have hz' : galoisGroupIntegerRingEquivOfIsIntegralClosure K L
      (abelianLocalArtinMap K L π) x = z := by
    apply Subtype.ext
    exact (galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L
      (abelianLocalArtinMap K L π) x).trans hz.symm
  change galoisGroupResidueAlgEquivOfIsIntegralClosure K L
      (abelianLocalArtinMap K L π) (IsLocalRing.residue 𝒪[L] x) =
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
      (arithmeticFrobeniusOfUnramifiedValuation K L) (IsLocalRing.residue 𝒪[L] x)
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply]
  change IsLocalRing.residue 𝒪[L]
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (abelianLocalArtinMap K L π) x) = _
  rw [hz']
  exact hres

/-- In an unramified extension the specified Artin map kills the actual
valuation-ring units, since their residue action is trivial and faithful. -/
theorem abelianLocalArtinMonoidHom_integerUnit_eq_one (a : 𝒪[K]ˣ) :
    abelianLocalArtinMonoidHom K L (integerUnitsToFieldUnits K a) = 1 := by
  have ha : integerUnitsToFieldUnits K a ∈ fieldPrincipalUnits K 0 := by
    change integerUnitsToFieldUnits K a ∈
      (principalUnits K 0).map (integerUnitsToFieldUnits K)
    rw [principalUnits_zero]
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top _, rfl⟩
  have hres : abelianLocalArtinMonoidHom K L (integerUnitsToFieldUnits K a) ∈
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
    rw [← abelianLocalArtinMonoidHom_units_eq_residue_ker K L]
    exact Subgroup.mem_map.mpr ⟨integerUnitsToFieldUnits K a, ha, rfl⟩
  apply galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L
  exact (MonoidHom.mem_ker.mp hres).trans
    (map_one (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)).symm

/-- For arbitrary field universes, the same Artin map is actual arithmetic
Frobenius raised to the normalized valuation of its input. -/
theorem abelianLocalArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    abelianLocalArtinMonoidHom K L x =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        valuationMap K (Additive.ofMul x) := by
  obtain ⟨a, ha⟩ := valuationMap_surjective K (1 : ℤ)
  let π : Kˣ := Additive.toMul a
  have hπ : valuationMap K (Additive.ofMul π) = 1 := ha
  have hArtin : abelianLocalArtinMonoidHom K L π =
      arithmeticFrobeniusOfUnramifiedValuation K L :=
    abelianLocalArtinMap_uniformizer K L π hπ
  calc
    abelianLocalArtinMonoidHom K L x =
        abelianLocalArtinMonoidHom K L
          (integerUnitsToFieldUnits K (uniformizerUnitFactor K π hπ x) *
            π ^ valuationMap K (Additive.ofMul x)) :=
      congrArg (abelianLocalArtinMonoidHom K L)
        (uniformizerUnitFactor_mul_uniformizer_zpow K π hπ x).symm
    _ = (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        valuationMap K (Additive.ofMul x) := by
      rw [map_mul, map_zpow, abelianLocalArtinMonoidHom_integerUnit_eq_one,
        one_mul, hArtin]

/-- The explicit unramified norm-quotient construction evaluates to the same
specified Artin automorphism on every representative, in independent universes. -/
theorem unramifiedLocalReciprocityIsoToGaloisGroup_normClass_eq_artin (x : Kˣ) :
    _root_.LocalClassFieldTheory.unramifiedLocalReciprocityIsoToGaloisGroup K L
        (normClass K L x) = abelianLocalArtinMonoidHom K L x := by
  rw [_root_.LocalClassFieldTheory.unramifiedLocalReciprocityIsoToGaloisGroup_normClass,
    abelianLocalArtinMonoidHom_eq_frobenius_zpow]

/-- A DVR prime element maps to inverse arithmetic Frobenius, preserving the original convention. -/
theorem abelianLocalArtinMap_uniformizerFieldUnit
    (π : 𝒪[K]) (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    abelianLocalArtinMap K L (uniformizerFieldUnit K π hπ) =
      (arithmeticFrobeniusOfUnramifiedValuation K L)⁻¹ := by
  have hval : valuationMap K (Additive.ofMul (uniformizerFieldUnit K π hπ)⁻¹) = 1 := by
    calc
      _ = -(valuationMap K (Additive.ofMul (uniformizerFieldUnit K π hπ))) :=
        valuationMap_ofMul_inv K _
      _ = -(-1 : ℤ) := congrArg Neg.neg (valuationMap_uniformizerFieldUnit K π hπ)
      _ = 1 := rfl
  have h := congrArg (fun σ : Gal(L / K) => σ⁻¹)
    (abelianLocalArtinMap_uniformizer K L (uniformizerFieldUnit K π hπ)⁻¹ hval)
  rw [map_inv, inv_inv] at h
  exact h

/-- The actual residue action uniquely characterizes the inverse-uniformizer
value of the same Artin map in independent field universes. -/
theorem abelianLocalArtinMap_inverseUniformizer_residue_pow_iff
    (π : 𝒪[K]) (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (σ : Gal(L/K)) :
    (∀ x : 𝒪[L], ∃ z : 𝒪[L],
      (z : L) = σ (x : L) ∧
        IsLocalRing.residue 𝒪[L] z = (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K]) ↔
      σ = abelianLocalArtinMap K L ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) := by
  let a : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹
  have ha : valuationMap K (Additive.ofMul a) = 1 := by
    change valuationMap K (Additive.ofMul (uniformizerFieldUnit K π hπ)⁻¹) = 1
    calc
      _ = -(valuationMap K (Additive.ofMul (uniformizerFieldUnit K π hπ))) :=
        valuationMap_ofMul_inv K _
      _ = -(-1 : ℤ) := congrArg Neg.neg (valuationMap_uniformizerFieldUnit K π hπ)
      _ = 1 := rfl
  have hArtin := abelianLocalArtinMap_inverseUniformizer_residue_pow K L a ha
  constructor
  · intro hσ
    apply galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨zσ, hzσ, hresσ⟩ := hσ x
    obtain ⟨za, hza, hresa⟩ := hArtin x
    have hzσ' : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x = zσ := by
      apply Subtype.ext
      exact (galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ x).trans hzσ.symm
    have hza' : galoisGroupIntegerRingEquivOfIsIntegralClosure K L
        (abelianLocalArtinMap K L a) x = za := by
      apply Subtype.ext
      exact (galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L
        (abelianLocalArtinMap K L a) x).trans hza.symm
    change IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
      IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (abelianLocalArtinMap K L a) x)
    rw [hzσ', hza']
    exact hresσ.trans hresa.symm
  · rintro rfl
    exact hArtin

end ActualFrobenius

end LocalClassFieldTheory.Universe
