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

section IndependentUniverses

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsUnramifiedValuedExtension K L]

/-- The specified Artin map acts by arithmetic Frobenius on the actual residues of an unramified
extension. Value one is the inverse-DVR-uniformizer convention of the original native map. -/
theorem abelianLocalArtinMap_inverseUniformizer_residue_pow
    (π : Kˣ) (hπ : valuationMap K (Additive.ofMul π) = 1) (x : 𝒪[L]) :
    ∃ z : 𝒪[L],
      (z : L) = abelianLocalArtinMap K L π (x : L) ∧
        IsLocalRing.residue 𝒪[L] z = (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  exact ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow K L π hπ x

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
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  exact ClassFieldTheory.finiteAbelianLocalArtinMap_uniformizer K L π hπ

/-- Arithmetic Frobenius raised to the normalized valuation gives the specified Artin value. -/
theorem abelianLocalArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    abelianLocalArtinMonoidHom K L x =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        valuationMap K (Additive.ofMul x) := by
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  exact _root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow K L x

/-- In an unramified extension the Artin map kills integral units, which have valuation zero. -/
theorem abelianLocalArtinMonoidHom_integerUnit_eq_one (a : 𝒪[K]ˣ) :
    abelianLocalArtinMonoidHom K L (integerUnitsToFieldUnits K a) = 1 := by
  have ha : valuationMap K (Additive.ofMul (integerUnitsToFieldUnits K a)) = 0 :=
    (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero K _).mp ⟨a, rfl⟩
  rw [abelianLocalArtinMonoidHom_eq_frobenius_zpow, ha, zpow_zero]

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
