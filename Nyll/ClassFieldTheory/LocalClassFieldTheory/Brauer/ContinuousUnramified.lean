/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.UnramifiedInvariant
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryRestriction

/-!
# The invariant of the continuous relative Brauer group

The finite-stage invariant applies to the same continuous classes that
inflate to absolute cohomological Brauer classes. The group and field-unit
actions in the comparison are the original ones.
-/

@[expose] public section

open scoped ValuativeRel
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ClassFieldTower.Cohomology

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]

section Galois

variable [IsGalois K L]

/-- The arithmetic carry class of a base unit in continuous relative H². -/
def unramifiedContinuousClass : Additive Kˣ →+ continuousCohomology 2 (galoisUnitsRep K L) :=
  (continuousRelativeUnitsH2Equiv K L).symm.toAddMonoidHom.comp (unramifiedClass K L)

/-- The finite-stage invariant on actual continuous relative classes. -/
def unramifiedContinuousInvariant : continuousCohomology 2 (galoisUnitsRep K L) →+
    AddCircle (1 : ℚ) :=
  (unramifiedInvariant K L).comp (continuousRelativeUnitsH2Equiv K L).toAddMonoidHom

/-- The continuous invariant keeps the arithmetic valuation formula on
actual carry representatives. -/
@[simp]
theorem unramifiedContinuousInvariant_class (a : Kˣ) :
    unramifiedContinuousInvariant K L (unramifiedContinuousClass K L (Additive.ofMul a)) =
      (((-valuationMap K (Additive.ofMul a) : ℤ) : ℚ) / Module.finrank K L : ℚ) := by
  change unramifiedInvariant K L ((continuousRelativeUnitsH2Equiv K L)
    ((continuousRelativeUnitsH2Equiv K L).symm (unramifiedClass K L (Additive.ofMul a)))) = _
  rw [AddEquiv.apply_symm_apply, unramifiedInvariant_class]

/-- The continuous finite-stage invariant is injective. -/
theorem unramifiedContinuousInvariant_injective :
    Function.Injective (unramifiedContinuousInvariant K L) :=
  (unramifiedInvariant_injective K L).comp (continuousRelativeUnitsH2Equiv K L).injective

/-- The degree-torsion range is retained by the continuous relative group. -/
theorem mem_range_unramifiedContinuousInvariant_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (unramifiedContinuousInvariant K L).range ↔ Module.finrank K L • x = 0 := by
  rw [← mem_range_unramifiedInvariant_iff K L x]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨continuousRelativeUnitsH2Equiv K L c, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨(continuousRelativeUnitsH2Equiv K L).symm c, ?_⟩
    change unramifiedInvariant K L ((continuousRelativeUnitsH2Equiv K L)
      ((continuousRelativeUnitsH2Equiv K L).symm c)) = _
    rw [AddEquiv.apply_symm_apply]

/-- The same arithmetic uniformizer value holds on the actual continuous
relative class. -/
theorem unramifiedContinuousInvariant_uniformizer :
    unramifiedContinuousInvariant K L
      (unramifiedContinuousClass K L (Additive.ofMul (integerRingUniformizerFieldUnit K))) =
        ((1 : ℚ) / Module.finrank K L : ℚ) := by
  rw [unramifiedContinuousInvariant_class, valuationMap_apply, v_integerRingUniformizerFieldUnit,
    neg_neg, Int.cast_one]

end Galois

/-- The arithmetic character of a specified cyclic generator takes it to
the reciprocal of the order of the group. -/
def finiteCyclicArithmeticCharacter {G : Type v} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : Additive G →+ AddCircle (1 : ℚ) where
  toFun x := zmodToRationalCircle (Nat.card G) Nat.card_pos
    (finiteCyclicGeneratorCoordinate g hg x.toMul)
  map_zero' := by rw [show (0 : Additive G).toMul = 1 from rfl,
    finiteCyclicGeneratorCoordinate_one, map_zero]
  map_add' x y := by rw [show (x + y).toMul = x.toMul * y.toMul from rfl,
    finiteCyclicGeneratorCoordinate_mul, map_add]

/-- The arithmetic character is faithful on its finite cyclic group. -/
theorem finiteCyclicArithmeticCharacter_injective {G : Type v} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Function.Injective (finiteCyclicArithmeticCharacter g hg) :=
  (zmodToRationalCircle_injective (Nat.card G) Nat.card_pos).comp
    ((finiteCyclicGeneratorCoordinate_injective g hg).comp Additive.toMul.injective)

/-- The arithmetic character takes every value killed by the group order. -/
theorem mem_range_finiteCyclicArithmeticCharacter_iff {G : Type v} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (z : AddCircle (1 : ℚ)) :
    z ∈ (finiteCyclicArithmeticCharacter g hg).range ↔ Nat.card G • z = 0 := by
  rw [← mem_range_zmodToRationalCircle_iff (Nat.card G) Nat.card_pos z]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨finiteCyclicGeneratorCoordinate g hg x.toMul, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨Additive.ofMul (g ^ x.val), ?_⟩
    change zmodToRationalCircle (Nat.card G) Nat.card_pos
      (finiteCyclicGeneratorCoordinate g hg (g ^ x.val)) = _
    rw [finiteCyclicGeneratorCoordinate_pow, ZMod.natCast_zmod_val]

theorem finiteCyclicArithmeticCharacter_apply {G : Type v} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul x) =
      (((finiteCyclicGeneratorCoordinate g hg x).val : ℚ) / Nat.card G : ℚ) := by
  let a := (finiteCyclicGeneratorCoordinate g hg x).val
  have he : (a : ZMod (Nat.card G)) = finiteCyclicGeneratorCoordinate g hg x :=
    ZMod.natCast_zmod_val _
  change zmodToRationalCircle (Nat.card G) Nat.card_pos (finiteCyclicGeneratorCoordinate g hg x) =
    ((a : ℚ) / Nat.card G : ℚ)
  rw [← he]
  simpa only [Int.cast_natCast] using zmodToRationalCircle_intCast (Nat.card G) Nat.card_pos (a : ℤ)

/-- Restricting a cyclic character to the subgroup specified by an
index power gives its character on the specified generator. -/
theorem finiteCyclicArithmeticCharacter_map_of_generator_power
    {G : Type u} {H : Type v} [Group G] [Fintype G] [Group H] [Fintype H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (f : H →* G) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card G = d * Nat.card H) (hf : f h = g ^ d) (x : H) :
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul (f x)) =
      finiteCyclicArithmeticCharacter h hh (Additive.ofMul x) := by
  rw [finiteCyclicArithmeticCharacter_apply, finiteCyclicArithmeticCharacter_apply,
    finiteCyclicGeneratorCoordinate_map_val g hg h hh f d hd hcard hf x, hcard]
  apply congrArg (fun q : ℚ => (q : AddCircle (1 : ℚ)))
  push_cast
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hH : (Nat.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'
  field_simp [hd', hH]

/-- On an unramified stage the arithmetic carry invariant is the value of
the Frobenius character at the inverse of the existing local Artin symbol. -/
theorem unramifiedContinuousInvariant_class_eq_artin [IsAbelianGalois K L] (a : Kˣ) :
    unramifiedContinuousInvariant K L (unramifiedContinuousClass K L (Additive.ofMul a)) =
      finiteCyclicArithmeticCharacter (arithmeticFrobeniusOfUnramifiedValuation K L)
        (arithmeticFrobeniusOfUnramifiedValuation_generates K L)
        (Additive.ofMul ((LocalClassFieldTheory.abelianLocalArtinMap K L a)⁻¹)) := by
  rw [unramifiedContinuousInvariant_class]
  change _ = zmodToRationalCircle (Nat.card Gal(L/K)) Nat.card_pos
    (finiteCyclicGeneratorCoordinate (arithmeticFrobeniusOfUnramifiedValuation K L)
      (arithmeticFrobeniusOfUnramifiedValuation_generates K L)
      (((LocalClassFieldTheory.abelianLocalArtinMap K L).toMonoidHom a)⁻¹))
  rw [LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom,
    LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_eq_frobenius_zpow, ← zpow_neg,
    finiteCyclicGeneratorCoordinate_zpow, zmodToRationalCircle_intCast,
    IsGalois.card_aut_eq_finrank K L]

/-- The value of the same cyclic character expressed using a second
generator. -/
theorem finiteCyclicArithmeticCharacter_changeGenerator
    {G : Type v} [Group G] [Fintype G]
    (g h : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hh : ∀ x : G, x ∈ Subgroup.zpowers h) (x : G) :
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul x) =
      (finiteCyclicGeneratorCoordinate g hg h).val •
        finiteCyclicArithmeticCharacter h hh (Additive.ofMul x) := by
  let q := zmodToRationalCircle (Nat.card G) Nat.card_pos
  change q (finiteCyclicGeneratorCoordinate g hg x) =
    (finiteCyclicGeneratorCoordinate g hg h).val • q (finiteCyclicGeneratorCoordinate h hh x)
  rw [finiteCyclicGeneratorCoordinate_change g hg h hh x, ← map_nsmul, nsmul_eq_mul,
    ZMod.natCast_zmod_val]

/-- Unramified carry classes use the same Artin evaluation for any
specified generator, with its own cyclic character. -/
theorem unramifiedContinuousInvariant_cyclicClass_eq_artin
    [IsAbelianGalois K L] [IsCyclic Gal(L/K)]
    (g : Gal(L/K)) (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) (a : Kˣ) :
    unramifiedContinuousInvariant K L (cyclicContinuousUnitClass K L g hg (Additive.ofMul a)) =
      finiteCyclicArithmeticCharacter g hg
        (Additive.ofMul ((LocalClassFieldTheory.abelianLocalArtinMap K L a)⁻¹)) := by
  let h := arithmeticFrobeniusOfUnramifiedValuation K L
  let hh := arithmeticFrobeniusOfUnramifiedValuation_generates K L
  rw [cyclicContinuousUnitClass_changeGenerator K L g hg h hh a, map_nsmul,
    finiteCyclicArithmeticCharacter_changeGenerator g h hg hh]
  apply congrArg ((finiteCyclicGeneratorCoordinate g hg h).val • ·)
  exact unramifiedContinuousInvariant_class_eq_artin K L a

end ClassFieldTheory.Brauer
