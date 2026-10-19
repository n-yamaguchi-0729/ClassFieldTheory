/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ArtinSchreierBound

/-!
# Artin–Schreier conductor bounds at characteristic-divisible depths

The explicit integral-element ramification bound, followed by the existing
filtered local reciprocity theorem, places all sufficiently deep principal
units in the actual field norm subgroup.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory.LocalField
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- If the parameter has pole order at most p n, the conductor of the
actual Artin–Schreier extension is at most p n. -/
theorem artinSchreier_localConductorExponent_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (a : K) (ha : (π : K) ^ (p * n) * a ∈ 𝒪[K])
    (β : L) (hβ : β ^ p - β = algebraMap K L a)
    (hgen : Algebra.adjoin K {β} = ⊤) :
    localConductorExponent K L ≤ p * n := by
  have hupper : localUpperRamificationGroup K L (p * n : ℕ) = ⊥ :=
    RamificationTheory.HilbertRamification.Higher.upperRamificationGroup_artinSchreier_eq_bot
      (localCompleteDVF K) (chosenLocalExtensionCompleteDVF K L) p π hπ n a ha β hβ hgen
  have hstep : artinPrincipalUnitStepGroup K L (p * n : ℕ) =
      artinPrincipalUnitGroup K L (p * n) := by
    change artinPrincipalUnitGroup K L ⌈((p * n : ℕ) : ℝ)⌉₊ = _
    rw [Nat.ceil_natCast]
  apply (artinPrincipalUnitGroup_eq_bot_iff K L (p * n)).mp
  rw [← hstep, finiteAbelian_filteredLocalReciprocity K L _ (Nat.cast_nonneg _), hupper]

/-- Every principal unit at a characteristic-divisible pole bound is an
actual norm from the Artin–Schreier extension. -/
theorem artinSchreier_fieldPrincipalUnits_le_norm
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (a : K) (ha : (π : K) ^ (p * n) * a ∈ 𝒪[K])
    (β : L) (hβ : β ^ p - β = algebraMap K L a)
    (hgen : Algebra.adjoin K {β} = ⊤) :
    fieldPrincipalUnits K (p * n) ≤ localNormSubgroup K L :=
  (localConductorExponent_le_iff K L (p * n)).mp
    (artinSchreier_localConductorExponent_le K L p π hπ n a ha β hβ hgen)

end LocalClassFieldTheory
