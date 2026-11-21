/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega

/-!
# Inflation of cyclic carry classes

For generator-preserving cyclic quotient maps, inflation of the carry class
scales its fixed coefficient by the index. The difference of the two carry
cocycles is the boundary of the explicit quotient-coordinate cochain.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Cohomology

universe u

section CoordinateBalance

private theorem zmodCarry_balance {n : ℕ} [NeZero n] (x y : ZMod n) :
    n * zmodCarry x y + (x + y).val = x.val + y.val := by
  by_cases h : n ≤ x.val + y.val
  · rw [(zmodCarry_eq_one_iff x y).mpr h, mul_one, ZMod.val_add_of_le h]
    omega
  · have h' := Nat.lt_of_not_ge h
    rw [(zmodCarry_eq_zero_iff x y).mpr h', mul_zero, zero_add, ZMod.val_add_of_lt h']

variable {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
variable (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
variable (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
variable (f : H →* G) (hf : f h = g)

include hf in
private theorem generatorCoordinate_map_val (x : H) :
    (finiteCyclicGeneratorCoordinate g hg (f x)).val =
      (finiteCyclicGeneratorCoordinate h hh x).val % Nat.card G := by
  let n := (finiteCyclicGeneratorCoordinate h hh x).val
  have hx : f x = g ^ n := by
    rw [← hf, ← map_pow, finiteCyclicGenerator_zpow_coordinate]
  rw [hx, finiteCyclicGeneratorCoordinate_pow, ZMod.val_natCast]

/-- The integer carry is the difference between the sum of the two
standard representatives and the representative of their group product. -/
theorem finiteCyclicCarry_balance (x y : G) :
    Nat.card G * finiteCyclicCarry g hg x y +
        (finiteCyclicGeneratorCoordinate g hg (x * y)).val =
      (finiteCyclicGeneratorCoordinate g hg x).val +
        (finiteCyclicGeneratorCoordinate g hg y).val := by
  let : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  rw [finiteCyclicGeneratorCoordinate_mul]
  exact zmodCarry_balance (finiteCyclicGeneratorCoordinate g hg x)
    (finiteCyclicGeneratorCoordinate g hg y)

include hf in
private theorem finiteCyclicCarry_quotient_balance (d : ℕ)
    (hcard : Nat.card H = d * Nat.card G) (x y : H) :
    let q : H → ℤ := fun z => ((finiteCyclicGeneratorCoordinate h hh z).val / Nat.card G : ℕ)
    (finiteCyclicCarry g hg (f x) (f y) : ℤ) + q x + q y =
      (finiteCyclicCarry h hh x y : ℤ) * d + q (x * y) := by
  intro q
  let n := Nat.card G
  let c (z : H) := (finiteCyclicGeneratorCoordinate h hh z).val
  let c' (z : H) := (finiteCyclicGeneratorCoordinate g hg (f z)).val
  have hdiv (z : H) : (c' z : ℤ) + (n : ℤ) * q z = (c z : ℤ) := by
    change (c' z : ℤ) + (n : ℤ) * ((c z / n : ℕ) : ℤ) = (c z : ℤ)
    exact_mod_cast ((congrArg (fun k : ℕ => k + n * (c z / n))
      (generatorCoordinate_map_val g hg h hh f hf z)).trans (Nat.mod_add_div (c z) n))
  have hg' : (n : ℤ) * (finiteCyclicCarry g hg (f x) (f y) : ℤ) + c' (x * y) =
      c' x + c' y := by
    have hg₀ := finiteCyclicCarry_balance g hg (f x) (f y)
    rw [← map_mul] at hg₀
    exact_mod_cast hg₀
  have hh' : ((d * n : ℕ) : ℤ) * (finiteCyclicCarry h hh x y : ℤ) + c (x * y) = c x + c y := by
    rw [show d * n = Nat.card H from hcard.symm]
    exact_mod_cast finiteCyclicCarry_balance h hh x y
  rw [Nat.cast_mul] at hh'
  have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  apply mul_left_cancel₀ hn
  linear_combination hg' + hdiv x + hdiv y - hdiv (x * y) - hh'

end CoordinateBalance

section GeneratorChange

variable {G : Type u} [Group G] [Fintype G]
  (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  (h : G) (hh : ∀ x : G, x ∈ Subgroup.zpowers h)

theorem finiteCyclicGeneratorCoordinate_change (x : G) :
    finiteCyclicGeneratorCoordinate g hg x =
      finiteCyclicGeneratorCoordinate g hg h * finiteCyclicGeneratorCoordinate h hh x := by
  let c := finiteCyclicGeneratorCoordinate h hh x
  have hx : x = h ^ c.val := (finiteCyclicGenerator_zpow_coordinate h hh x).symm
  calc
    _ = finiteCyclicGeneratorCoordinate g hg (h ^ c.val) :=
      congrArg (finiteCyclicGeneratorCoordinate g hg) hx
    _ = c.val • finiteCyclicGeneratorCoordinate g hg h := by
      rw [finiteCyclicGeneratorCoordinate, map_pow]
      rfl
    _ = _ := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

private theorem finiteCyclicCarry_change_balance (x y : G) :
    let c := (finiteCyclicGeneratorCoordinate g hg h).val
    let q : G → ℤ := fun z => ((c * (finiteCyclicGeneratorCoordinate h hh z).val) / Nat.card G : ℕ)
    (finiteCyclicCarry g hg x y : ℤ) + q x + q y =
      (c : ℤ) * (finiteCyclicCarry h hh x y : ℤ) + q (x * y) := by
  intro c q
  let n := Nat.card G
  let a (z : G) := (finiteCyclicGeneratorCoordinate g hg z).val
  let b (z : G) := (finiteCyclicGeneratorCoordinate h hh z).val
  have hmod (z : G) : a z = (c * b z) % n := by
    change (finiteCyclicGeneratorCoordinate g hg z).val = _
    rw [finiteCyclicGeneratorCoordinate_change g hg h hh z]
    rw [← ZMod.natCast_zmod_val (n := n) (finiteCyclicGeneratorCoordinate g hg h),
      ← ZMod.natCast_zmod_val (n := n) (finiteCyclicGeneratorCoordinate h hh z),
      ← Nat.cast_mul, ZMod.val_natCast]
  have hdiv (z : G) : (a z : ℤ) + (n : ℤ) * q z = (c : ℤ) * (b z : ℤ) := by
    change (a z : ℤ) + (n : ℤ) * (((c * b z) / n : ℕ) : ℤ) = _
    exact_mod_cast ((congrArg (fun m : ℕ => m + n * ((c * b z) / n)) (hmod z)).trans
      (Nat.mod_add_div (c * b z) n))
  have ha : (n : ℤ) * (finiteCyclicCarry g hg x y : ℤ) + (a (x * y) : ℤ) =
      (a x : ℤ) + (a y : ℤ) := by
    exact_mod_cast finiteCyclicCarry_balance g hg x y
  have hb : (n : ℤ) * (finiteCyclicCarry h hh x y : ℤ) + (b (x * y) : ℤ) =
      (b x : ℤ) + (b y : ℤ) := by
    exact_mod_cast finiteCyclicCarry_balance h hh x y
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne')
  linear_combination ha + hdiv x + hdiv y - hdiv (x * y) - (c : ℤ) * hb

end GeneratorChange

section GeneratorChangeClass

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
  (A : Rep R G)
  (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  (h : G) (hh : ∀ x : G, x ∈ Subgroup.zpowers h)

/-- Changing the generator changes the carry class by the actual
coordinate of the new generator in the old character. -/
theorem finiteCyclicCarry_changeGenerator_eq_nsmul
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : LinearMap.ker (Rep.applyAsHom A h - 𝟙 A).hom.toLinearMap)
    (hab : a.1 = b.1) :
    groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a) =
      (finiteCyclicGeneratorCoordinate g hg h).val •
        groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A h hh b) := by
  let c := (finiteCyclicGeneratorCoordinate g hg h).val
  let q (z : G) : ℤ := ((c * (finiteCyclicGeneratorCoordinate h hh z).val) / Nat.card G : ℕ)
  let w := finiteCyclicCarryTwoCocycle A g hg a - c • finiteCyclicCarryTwoCocycle A h hh b
  have ha : A.ρ g a.val - a.val = 0 := a.property
  have hfix (σ : G) : A.ρ σ a.val = a.val :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg a.val).2
      (sub_eq_zero.mp ha) σ
  have hw : groupCohomology.H2π A w = 0 := by
    apply (groupCohomology.H2π_eq_zero_iff w).2
    refine ⟨fun x => -(q x • a.val), funext ?_⟩
    rintro ⟨x, y⟩
    change A.ρ x (-(q y • a.val)) - -(q (x * y) • a.val) + -(q x • a.val) =
      finiteCyclicCarry g hg x y • a.val - c • (finiteCyclicCarry h hh x y • b.val)
    rw [map_neg, map_zsmul, hfix, ← hab]
    have hsum := congrArg (fun m : ℤ => m • a.val) (finiteCyclicCarry_change_balance g hg h hh x y)
    change ((finiteCyclicCarry g hg x y : ℤ) + q x + q y) • a.val =
      ((c : ℤ) * (finiteCyclicCarry h hh x y : ℤ) + q (x * y)) • a.val at hsum
    simp only [add_zsmul, mul_zsmul, natCast_zsmul] at hsum
    have hd := congrArg (fun z : A => z - q x • a.val - q y • a.val -
      c • (finiteCyclicCarry h hh x y • a.val)) hsum
    calc
      _ = (c • (finiteCyclicCarry h hh x y • a.val) + q (x * y) • a.val) -
          q x • a.val - q y • a.val - c • (finiteCyclicCarry h hh x y • a.val) := by abel
      _ = (finiteCyclicCarry g hg x y • a.val + q x • a.val + q y • a.val) -
          q x • a.val - q y • a.val - c • (finiteCyclicCarry h hh x y • a.val) := hd.symm
      _ = _ := by abel
  rw [← map_nsmul, ← sub_eq_zero, ← map_sub]
  exact hw

end GeneratorChangeClass

variable {R G H : Type u} [CommRing R] [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
variable (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
variable (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
variable (f : H →* G) (hf : f h = g)

include hf in
/-- Under a cyclic quotient sending the specified generator to the specified
generator, inflation of the original carry class multiplies its coefficient
by the ratio of the group orders. -/
theorem finiteCyclicCarry_inflation_eq_class
    (A : Rep R G) (B : Rep R H) (φ : Rep.res f A ⟶ B)
    (d : ℕ) (hcard : Nat.card H = d * Nat.card G)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : LinearMap.ker (Rep.applyAsHom B h - 𝟙 B).hom.toLinearMap)
    (hb : b.1 = d • φ.hom a.1) :
    groupCohomology.map f φ 2
        (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) =
      groupCohomology.H2π B (finiteCyclicCarryTwoCocycle B h hh b) := by
  let q : H → ℤ := fun z => ((finiteCyclicGeneratorCoordinate h hh z).val / Nat.card G : ℕ)
  let v : B := φ.hom a.1
  have ha : a.1 ∈ A.ρ.invariants := by
    apply (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg a.1).mpr
    have ha₀ := a.2
    change A.ρ g a.1 - a.1 = 0 at ha₀
    exact sub_eq_zero.mp ha₀
  have hv (x : H) : B.ρ x v = v := by
    change B.ρ x (φ.hom a.1) = φ.hom a.1
    rw [← Rep.hom_comm_apply]
    change φ.hom (A.ρ (f x) a.1) = φ.hom a.1
    rw [ha (f x)]
  let z := groupCohomology.mapCocycles₂ f φ (finiteCyclicCarryTwoCocycle A g hg a) -
    finiteCyclicCarryTwoCocycle B h hh b
  have hz : groupCohomology.H2π B z = 0 := by
    apply (groupCohomology.H2π_eq_zero_iff z).mpr
    refine ⟨fun x => -(q x • v), funext (fun p => ?_)⟩
    obtain ⟨x, y⟩ := p
    change B.ρ x (-(q y • v)) - -(q (x * y) • v) + -(q x • v) =
      φ.hom (finiteCyclicCarry g hg (f x) (f y) • a.1) - finiteCyclicCarry h hh x y • b.1
    rw [map_neg, map_zsmul, hv, map_nsmul, hb]
    have hsum := congrArg (fun m : ℤ => m • v)
      (finiteCyclicCarry_quotient_balance g hg h hh f hf d hcard x y)
    change ((finiteCyclicCarry g hg (f x) (f y) : ℤ) + q x + q y) • v =
      ((finiteCyclicCarry h hh x y : ℤ) * d + q (x * y)) • v at hsum
    simp only [add_zsmul, mul_zsmul, natCast_zsmul] at hsum
    have hdiff := congrArg (fun w : B => w - q x • v - q y • v -
      finiteCyclicCarry h hh x y • (d • v)) hsum
    calc
      _ = (finiteCyclicCarry h hh x y • (d • v) + q (x * y) • v) - q x • v - q y • v -
          finiteCyclicCarry h hh x y • (d • v) := by abel
      _ = (finiteCyclicCarry g hg (f x) (f y) • v + q x • v + q y • v) - q x • v - q y • v -
          finiteCyclicCarry h hh x y • (d • v) := hdiff.symm
      _ = _ := by abel
  rw [groupCohomology.H2π_comp_map_apply, ← sub_eq_zero, ← map_sub]
  exact hz

end ClassFieldTower.Cohomology
