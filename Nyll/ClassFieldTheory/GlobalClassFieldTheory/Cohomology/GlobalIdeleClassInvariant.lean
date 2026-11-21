/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.GlobalFundamentalClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified

/-! # The complete arithmetic invariant on original global degree-two cohomology -/

@[expose] public section

open ClassFieldTheory.Brauer ClassFieldTower.Cohomology

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

universe u v

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "H" =>
  IntegralGroupCohomology.Universe.cohomology (standardIdeleClassRep K L) 2
local notation "G" => Multiplicative H
local notation "g" => Multiplicative.ofAdd (globalFundamentalClass K L)
local instance globalIdeleClassGroupH2_finite : Finite G :=
  (originalStandardIdeleClassH2_finite_card K L).1
local instance globalIdeleClassGroupH2_fintype : Fintype G := Fintype.ofFinite G

/-- The arithmetic-normalized class generates the entire original degree-two group. -/
theorem globalFundamentalClass_generates : ∀ x : G, x ∈ Subgroup.zpowers g := by
  have hcard : Nat.card (Subgroup.zpowers g) = Nat.card G := by
    rw [Nat.card_zpowers]
    change addOrderOf (globalFundamentalClass K L) = Nat.card H
    rw [addOrderOf_globalFundamentalClass, (originalStandardIdeleClassH2_finite_card K L).2]
  have ht : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  intro x
  rw [ht]
  exact Subgroup.mem_top x

/-- The additive invariant sends the canonical class to the reciprocal degree. -/
def globalIdeleClassInvariant : H →+ AddCircle (1 : ℚ) :=
  finiteCyclicArithmeticCharacter g (globalFundamentalClass_generates K L)

/-- The arithmetic invariant detects the actual degree-two class. -/
theorem globalIdeleClassInvariant_injective :
    Function.Injective (globalIdeleClassInvariant K L) :=
  finiteCyclicArithmeticCharacter_injective g (globalFundamentalClass_generates K L)

/-- The image consists of exactly the rational-circle classes killed by the extension degree. -/
theorem mem_range_globalIdeleClassInvariant_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (globalIdeleClassInvariant K L).range ↔ Module.finrank K L • x = 0 := by
  change x ∈
    (finiteCyclicArithmeticCharacter g (globalFundamentalClass_generates K L)).range ↔ _
  rw [mem_range_finiteCyclicArithmeticCharacter_iff]
  change Nat.card H • x = 0 ↔ _
  rw [(originalStandardIdeleClassH2_finite_card K L).2]

/-- The reciprocal normalization is valid for every finite Galois extension of number fields. -/
theorem globalIdeleClassInvariant_fundamentalClass :
    globalIdeleClassInvariant K L (globalFundamentalClass K L) =
      ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  change zmodToRationalCircle (Nat.card G) Nat.card_pos
    (finiteCyclicGeneratorCoordinate g (globalFundamentalClass_generates K L) g) = _
  rw [finiteCyclicGeneratorCoordinate_generator]
  have hd : Nat.card G = Module.finrank K L := (originalStandardIdeleClassH2_finite_card K L).2
  simpa only [Int.cast_one, hd] using zmodToRationalCircle_intCast (Nat.card G) Nat.card_pos 1

end GlobalClassFieldTheory.Cohomology
