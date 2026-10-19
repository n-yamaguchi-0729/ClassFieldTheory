/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Carry coordinates under cyclic subgroup restriction

When the smaller generator maps to the index-th power of the larger one,
the normalized carry is unchanged. This is the explicit coefficient comparison
used for restricting a cyclic norm class to a decomposition group.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

/-- An injective map into a finite cyclic group admits a generator mapping
to exactly the index-th power of a specified generator. -/
theorem finiteCyclic_exists_generator_map_index
    {G H : Type u} [CommGroup G] [Finite G] [Group H] [Finite H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (f : H →* G) (hf : Function.Injective f) :
    ∃ h : H, (∀ x : H, x ∈ Subgroup.zpowers h) ∧ f h = g ^ f.range.index ∧
      Nat.card G = f.range.index * Nat.card H := by
  have hcardRange : Nat.card f.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hcard : Nat.card G = f.range.index * Nat.card H := by
    rw [← f.range.card_mul_index, hcardRange, Nat.mul_comm]
  have hd : f.range.index ≠ 0 := f.range.index_ne_zero_of_finite
  obtain ⟨h, hh⟩ := f.range.pow_index_mem g
  have horder : orderOf h = Nat.card H := by
    rw [← orderOf_injective f hf h, hh,
      orderOf_pow_of_dvd hd (by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
        exact dvd_mul_right _ _),
      orderOf_eq_card_of_forall_mem_zpowers hg, hcard,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]
  have htop : Subgroup.zpowers h = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers h)).mp
      ((Nat.card_zpowers h).trans horder)
  exact ⟨h, fun x => htop.ge (Subgroup.mem_top x), hh, hcard⟩

/-- Generator coordinates scale by the subgroup index, without modular wraparound. -/
theorem finiteCyclicGeneratorCoordinate_map_val
    {G H : Type u} [Group G] [Fintype G] [Group H] [Fintype H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card G = d * Nat.card H) (hf : f h = g ^ d) (x : H) :
    (finiteCyclicGeneratorCoordinate g hg (f x)).val =
      d * (finiteCyclicGeneratorCoordinate h hh x).val := by
  let i := (finiteCyclicGeneratorCoordinate h hh x).val
  have hx : f x = g ^ (d * i) := by
    calc
      f x = f (h ^ i) := congrArg f (finiteCyclicGenerator_zpow_coordinate h hh x).symm
      _ = (f h) ^ i := map_pow f h i
      _ = g ^ (d * i) := by rw [hf, pow_mul]
  have hi : d * i < Nat.card G := by
    rw [hcard]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt (finiteCyclicGeneratorCoordinate h hh x)) hd
  rw [hx, finiteCyclicGeneratorCoordinate_pow, ZMod.val_natCast,
    Nat.mod_eq_of_lt hi]

/-- The actual carry is preserved when a cyclic subgroup generator maps to the index power. -/
theorem finiteCyclicCarry_map_of_generator_power
    {G H : Type u} [Group G] [Fintype G] [Group H] [Fintype H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card G = d * Nat.card H) (hf : f h = g ^ d) (x y : H) :
    finiteCyclicCarry g hg (f x) (f y) = finiteCyclicCarry h hh x y := by
  simp only [finiteCyclicCarry, zmodCarry,
    finiteCyclicGeneratorCoordinate_map_val g hg h hh f d hd hcard hf,
    hcard, ← Nat.mul_add, mul_le_mul_iff_right₀ hd]

/-- Pullback preserves the actual carry cocycle when the generator is normalized
by the subgroup index and the coefficient is carried by the given morphism. -/
theorem finiteCyclicCarry_mapCocycles₂_of_generator_power
    {R G H : Type u} [CommRing R] [CommGroup G] [Fintype G]
    [CommGroup H] [Fintype H]
    (A : Rep R G) (B : Rep R H)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (φ : Rep.res f A ⟶ B) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card G = d * Nat.card H) (hf : f h = g ^ d)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : LinearMap.ker (Rep.applyAsHom B h - 𝟙 B).hom.toLinearMap)
    (hab : φ.hom a.1 = b.1) :
    groupCohomology.mapCocycles₂ f φ (finiteCyclicCarryTwoCocycle A g hg a) =
      finiteCyclicCarryTwoCocycle B h hh b := by
  apply Subtype.ext
  funext st
  change φ.hom (finiteCyclicCarry g hg (f st.1) (f st.2) • a.1) =
    finiteCyclicCarry h hh st.1 st.2 • b.1
  rw [map_nsmul, hab, finiteCyclicCarry_map_of_generator_power g hg h hh f d hd hcard hf]

end
end ClassFieldTower.Cohomology
