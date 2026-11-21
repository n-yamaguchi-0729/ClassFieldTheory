/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.RelativeDiscriminant
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness

/-! # The finite support shared by the conductor and relative discriminant -/

@[expose] public section

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

namespace GlobalClassFieldTheory.GlobalClassFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- A finite place occurs in the discriminant if and only if it occurs in the conductor. -/
theorem relativeDiscriminant_count_ne_zero_iff_mem_finiteConductor
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (AlgebraicNumberTheory.Discriminant.relativeDiscriminantIdeal K L :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔
      v ∈ (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support := by
  rw [AlgebraicNumberTheory.Discriminant.count_relativeDiscriminantIdeal_ne_zero_iff_ramified,
    ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces]
  exact (_root_.mem_ramifiedBaseFinitePlaces_iff (K := K) (L := L) v).symm

/-- A finite discriminant prime occurs in the conductor of at least one of the Galois characters. -/
theorem relativeDiscriminant_count_ne_zero_iff_exists_character
    (M : Type*) [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))]
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (AlgebraicNumberTheory.Discriminant.relativeDiscriminantIdeal K L :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔
      ∃ χ : Gal(L/K) →* Mˣ, (abelianCharacterConductor K L χ).finitePart v ≠ 0 := by
  classical
  let : Fintype (Gal(L/K) →* Mˣ) := Fintype.ofFinite _
  let c : (Gal(L/K) →* Mˣ) → ℕ := fun χ => (abelianCharacterConductor K L χ).finitePart v
  rw [relativeDiscriminant_count_ne_zero_iff_mem_finiteConductor, Finsupp.mem_support_iff]
  change (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.finitePart v ≠ 0 ↔
    ∃ χ, c χ ≠ 0
  rw [abelianFullConductor_finiteExponent_eq_sup_characterConductor K L M v]
  change Finset.univ.sup c ≠ 0 ↔ ∃ χ, c χ ≠ 0
  constructor
  · intro h
    by_contra hn
    apply h
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le_iff.mpr
    intro χ _
    have hχ : c χ = 0 := by
      by_contra hχ
      exact hn ⟨χ, hχ⟩
    exact hχ.le
  · rintro ⟨χ, hχ⟩ hsup
    have hle := Finset.le_sup (f := c) (Finset.mem_univ χ)
    rw [hsup] at hle
    exact hχ (Nat.eq_zero_of_le_zero hle)

end GlobalClassFieldTheory.GlobalClassFields
