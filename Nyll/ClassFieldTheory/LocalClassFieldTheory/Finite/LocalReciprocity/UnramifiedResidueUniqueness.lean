/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# Uniqueness of arithmetic Frobenius from its residue action

For an unramified finite abelian extension, the arithmetic `q`-power action
on residues determines the Galois automorphism uniquely.  The canonical local
Artin map takes an inverse uniformizer to this automorphism.
-/

@[expose] public section

universe u v

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

omit [IsUniformAddGroup L] in
/-- The residue `q`-power action characterizes the canonical local Artin
image of an inverse uniformizer in an unramified finite abelian extension. -/
theorem finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow_iff
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (σ : L ≃ₐ[K] L) :
    (∀ x : 𝒪[L],
      ∃ z : 𝒪[L],
        (z : L) = σ (x : L) ∧
          IsLocalRing.residue 𝒪[L] z =
            (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K]) ↔
      σ = LocalClassFieldTheory.Universe.abelianLocalArtinMap K L
        ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) := by
  let u : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹
  have hvalUnit :
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero)) = -1 :=
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
      K π hπ
  have hval :
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul u) = 1 := by
    calc
      _ = -LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero)) := by
            change
              LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
                  (-(Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))) = _
            exact
              LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_neg
                K (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))
      _ = 1 := by rw [hvalUnit]; norm_num
  have hArtin (x : 𝒪[L]) :=
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_inverseUniformizer_residue_pow
      K L u hval x
  constructor
  · intro hσ
    apply (open _root_.LocalFieldTheory in
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L)
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨zσ, hzσ, hresσ⟩ := hσ x
    obtain ⟨za, hza, hresa⟩ := hArtin x
    have hzσ' :
        LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L σ x = zσ := by
      apply Subtype.ext
      exact (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
        K L σ x).trans hzσ.symm
    have hza' :
        LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L (LocalClassFieldTheory.Universe.abelianLocalArtinMap K L u) x = za := by
      apply Subtype.ext
      exact (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
        K L (LocalClassFieldTheory.Universe.abelianLocalArtinMap K L u) x).trans hza.symm
    change IsLocalRing.residue 𝒪[L]
        (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L σ x) =
      IsLocalRing.residue 𝒪[L]
        (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          K L (LocalClassFieldTheory.Universe.abelianLocalArtinMap K L u) x)
    rw [hzσ', hza']
    exact hresσ.trans hresa.symm
  · intro hσ
    subst σ
    exact hArtin

end ClassFieldTheory
