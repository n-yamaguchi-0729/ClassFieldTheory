/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFiltered
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Core
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ArtinSchreierBound

/-!
# Artin–Schreier conductor bounds at characteristic-divisible depths

The explicit integral-element ramification bound, followed by the existing
filtered local reciprocity theorem, places all sufficiently deep principal
units in the actual field norm subgroup.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory.LocalField
open scoped ValuativeRel

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
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
  have hnorm : (Universe.abelianLocalArtinMonoidHom K L).ker = localNormSubgroup K L :=
    Universe.abelianLocalArtinMap_ker K L
  apply (localConductorExponent_le_iff K L (p * n)).mpr
  rw [← hnorm, ← Subgroup.map_eq_bot_iff]
  have hfiltered := Universe.finiteAbelian_filteredLocalReciprocity
    K L (p * n : ℕ) (Nat.cast_nonneg _)
  change (fieldPrincipalUnits K ⌈((p * n : ℕ) : ℝ)⌉₊).map
    (Universe.abelianLocalArtinMonoidHom K L) =
      localUpperRamificationGroup K L (p * n : ℕ) at hfiltered
  rw [Nat.ceil_natCast, hupper] at hfiltered
  exact hfiltered

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
