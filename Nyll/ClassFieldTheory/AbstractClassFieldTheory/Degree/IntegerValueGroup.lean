/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation

/-!
# The integer value group inside the profinite integers

For the actual image of the integers in `ZHat`, inclusion followed by
reduction induces the required canonical isomorphism modulo every positive
integer. The proof uses integer representatives and ordinary divisibility.
-/

namespace ClassFormation

/-- The actual subgroup of integral values inside the profinite integers. -/
def integerValueGroup : AddSubgroup ZHat := (Int.castRingHom ZHat).toAddMonoidHom.range

/-- The canonical valuation quotient map is bijective for the integer value group. -/
theorem canonicalValueQuotientMap_integer_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (canonicalValueQuotientMap integerValueGroup n hn) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    obtain ⟨a, ha⟩ := z₁.2
    obtain ⟨b, hb⟩ := z₂.2
    have hred : (a : ZMod n) = (b : ZMod n) := by
      change zHatReduction n hn z₁.1 = zHatReduction n hn z₂.1 at h
      rw [← ha, ← hb] at h
      exact h
    have hdvd : (n : ℤ) ∣ a - b :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) n).mp (by rw [Int.cast_sub, hred, sub_self])
    obtain ⟨m, hm⟩ := hdvd
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨⟨(m : ZHat), ⟨m, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change n • (m : ZHat) = z₁.1 - z₂.1
    rw [← ha, ← hb]
    change n • (m : ZHat) = (a : ZHat) - (b : ZHat)
    rw [← Int.cast_sub, hm, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  · intro x
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective x
    refine ⟨QuotientAddGroup.mk' (nsmulWithin integerValueGroup n)
      ⟨(m : ZHat), ⟨m, rfl⟩⟩, ?_⟩
    exact (zHatReduction_intCast n hn m).trans hm

end ClassFormation
