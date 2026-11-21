/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.Tactic.FinCases
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.RealInvariant
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.UnramifiedInvariant

/-! # The Brauer invariant at a real place -/

@[expose] public section

noncomputable section

namespace ClassFieldTheory.Brauer

variable {K : Type*} [Field K] [NumberField K]
    {v : NumberField.InfinitePlace K} (hv : v.IsReal)

/-- The local Brauer group at the given real place is the sign group. -/
def realPlaceBrauerSignEquiv : Br v.Completion ≃+ Additive ℤˣ :=
  realBrauerSignEquivOfRingEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)

/-- The sign of the original global class at the actual real completion. -/
def realPlaceRestrictionSign : Br K →+ Additive ℤˣ :=
  (realPlaceBrauerSignEquiv hv).toAddMonoidHom.comp (infinitePlaceRestriction K v)

/-- The sign group has coordinates zero and one in `ℤ/2ℤ`. -/
def realBrauerSignToZMod : Additive ℤˣ →+ ZMod 2 where
  toFun x := if x.toMul = 1 then 0 else 1
  map_zero' := ite_eq_left rfl
  map_add' x y := by
    change (if x.toMul * y.toMul = 1 then (0 : ZMod 2) else 1) =
      (if x.toMul = 1 then 0 else 1) + (if y.toMul = 1 then 0 else 1)
    rcases Int.units_eq_one_or x.toMul with hx | hx <;>
      rcases Int.units_eq_one_or y.toMul with hy | hy <;> rw [hx, hy] <;> decide

theorem realBrauerSignToZMod_bijective : Function.Bijective realBrauerSignToZMod := by
  constructor
  · intro x y h
    apply Additive.toMul.injective
    rcases Int.units_eq_one_or x.toMul with hx | hx <;>
      rcases Int.units_eq_one_or y.toMul with hy | hy
    · exact hx.trans hy.symm
    · change (if x.toMul = 1 then (0 : ZMod 2) else 1) =
        (if y.toMul = 1 then 0 else 1) at h
      rw [hx, hy] at h
      exact (by decide : ¬ ((if (1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) =
        (if (-1 : ℤˣ) = 1 then 0 else 1))) h |>.elim
    · change (if x.toMul = 1 then (0 : ZMod 2) else 1) =
        (if y.toMul = 1 then 0 else 1) at h
      rw [hx, hy] at h
      exact (by decide : ¬ ((if (1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) =
        (if (-1 : ℤˣ) = 1 then 0 else 1))) h.symm |>.elim
    · exact hx.trans hy.symm
  · intro x
    fin_cases x
    · exact ⟨Additive.ofMul 1, by
        change (if (1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 0
        exact ite_eq_left rfl⟩
    · exact ⟨Additive.ofMul (-1), by
        change (if (-1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 1
        exact ite_eq_right (by decide)⟩

/-- The real invariant of the original local Brauer group takes values in `ℚ/ℤ`. -/
def realPlaceBrauerInvariant : Br v.Completion →+ AddCircle (1 : ℚ) :=
  (zmodToRationalCircle 2 (by decide)).comp
    (realBrauerSignToZMod.comp (realPlaceBrauerSignEquiv hv).toAddMonoidHom)

omit [NumberField K] in
/-- A real Brauer class is detected by its local rational invariant. -/
theorem realPlaceBrauerInvariant_injective : Function.Injective (realPlaceBrauerInvariant hv) :=
  (zmodToRationalCircle_injective 2 (by decide)).comp
    (realBrauerSignToZMod_bijective.injective.comp (realPlaceBrauerSignEquiv hv).injective)

omit [NumberField K] in
/-- The image of the real invariant is exactly the two-torsion in `ℚ/ℤ`. -/
theorem mem_range_realPlaceBrauerInvariant_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (realPlaceBrauerInvariant hv).range ↔ 2 • x = 0 := by
  rw [← mem_range_zmodToRationalCircle_iff 2 (by decide)]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨realBrauerSignToZMod (realPlaceBrauerSignEquiv hv a), rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := realBrauerSignToZMod_bijective.surjective a
    obtain ⟨c, rfl⟩ := (realPlaceBrauerSignEquiv hv).surjective b
    exact ⟨c, rfl⟩

/-- The negative sign has invariant `1/2` in `ℚ/ℤ`. -/
theorem realBrauerSign_negative_invariant :
    zmodToRationalCircle 2 (by decide) (realBrauerSignToZMod (Additive.ofMul (-1 : ℤˣ))) =
      ((1 : ℚ) / 2 : ℚ) := by
  have h : realBrauerSignToZMod (Additive.ofMul (-1 : ℤˣ)) = (1 : ZMod 2) := by decide
  rw [h]
  have hr : ((1 : ℤ) : ℚ) / ((2 : ℕ) : ℚ) = (1 : ℚ) / 2 := by norm_num
  have hz : ((1 : ℤ) : ZMod 2) = 1 := Int.cast_one
  rw [← hz]
  exact (zmodToRationalCircle_intCast 2 (by decide) 1).trans
    (congrArg (fun q : ℚ => (q : AddCircle (1 : ℚ))) hr)

end ClassFieldTheory.Brauer
