/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
public import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Mathlib.NumberTheory.LocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology

/-!
# Local-field structure on a finite adic completion

The distinguished integer-valued valuation on a number-field completion
provides the valuation relation required by local reciprocity.  The
valuation relation is passed explicitly, not registered globally.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

section CompletionComparison

open LocalClassFieldTheory

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

local instance finitePlaceCompletionComparisonSourceValuativeRel :
    ValuativeRel (HeightOneSpectrum.adicAbv F v).Completion :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v

local instance finitePlaceCompletionComparisonTargetValuativeRel :
    ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v

/-- The canonical equivalence between the two finite-completion models
respects their chosen valuation relations. -/
theorem finitePlaceCompletion_semilinearValuationCompatible :
    SemilinearValuationCompatible
      (HeightOneSpectrum.adicAbv F v).Completion
      (v.adicCompletion F)
      (finitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let C' := v.adicCompletion F
  let e := (finitePlaceCompletionAlgEquiv v).toRingEquiv
  let _ : Algebra C C' := e.toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation C')
  constructor
  intro x y
  change ValuativeRel.valuation C x ≤ ValuativeRel.valuation C y ↔
    ValuativeRel.valuation C' (e x) ≤ ValuativeRel.valuation C' (e y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  change ‖x‖₊ ≤ ‖y‖₊ ↔
    (Valued.v : Valuation C' (WithZero (Multiplicative ℤ))) (e x) ≤ Valued.v (e y)
  rw [← Valued.toNormedField.norm_le_iff]
  change ‖x‖ ≤ ‖y‖ ↔ ‖finitePlaceCompletionRingEquiv v x‖ ≤
    ‖finitePlaceCompletionRingEquiv v y‖
  rw [finitePlaceCompletionRingEquiv_norm,
    finitePlaceCompletionRingEquiv_norm]

end CompletionComparison

namespace ClassFieldTheory

/-- At each finite place, transport the local Hilbert pairing from the
absolute-value completion to Mathlib's adic completion. -/
def finitePlaceAdicHilbertPairingFamily
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    GlobalHilbertPairingFamily F n := by
  intro v
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : CharZero C :=
    charZero_of_injective_algebraMap (algebraMap F C).injective
  have hnC : ((n : ℕ) : C) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr n.ne_zero
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap F C ζ,
      (mem_primitiveRoots n.pos).2
        (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
          (algebraMap F C).injective)⟩
  exact hilbertPairingOfRingEquiv
    (finitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
    (localHilbertPairing C n hnC hmuC)

/-- Every finite member of the transported family satisfies the local
Steinberg, skew-symmetry, nondegeneracy, and Kummer norm-residue laws. -/
theorem finitePlaceAdicHilbertPairingFamily_isLocallyHilbert
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    GlobalHilbertPairingFamily.IsLocallyHilbert F
      (finitePlaceAdicHilbertPairingFamily F n hmu) := by
  intro v
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  exact
    let : ValuativeRel C :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField C :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let : CharZero C :=
      charZero_of_injective_algebraMap (algebraMap F C).injective
    have hnC : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
    have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
      obtain ⟨ζ, hζ⟩ := hmu
      exact ⟨algebraMap F C ζ,
        (mem_primitiveRoots n.pos).2
          (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
            (algebraMap F C).injective)⟩
    show HilbertPairing.IsLocalHilbertPairing (hilbertPairingOfRingEquiv
      (finitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
      (localHilbertPairing C n hnC hmuC)) from
      hilbertPairingOfRingEquiv_isLocalHilbertPairing
        (finitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
        (localHilbertPairing C n hnC hmuC)
        (localHilbertPairing_isLocalHilbertPairing C n hnC hmuC)

end ClassFieldTheory
