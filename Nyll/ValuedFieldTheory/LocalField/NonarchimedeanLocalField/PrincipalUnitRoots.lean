/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.SchemeTheory.RingTheory.Henselian.HenselianUnitRoots

/-!
# Prime-to-residue roots in the actual principal-unit filtration

Adic completeness supplies Henselianity of the original integer ring. The
Hensel root remains congruent to one at the specified positive depth.
-/

@[expose] public section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u

/-- Every principal unit at positive depth has a root of any degree which is
a unit in the integer ring, at the same depth and in the same unit group. -/
theorem exists_principalUnit_pow_eq_of_isUnit_natCast
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : IsUnit (d : 𝒪[K])) {r : ℕ} (hr : 1 ≤ r)
    {a : 𝒪[K]ˣ} (ha : a ∈ principalUnits K r) :
    ∃ z : 𝒪[K]ˣ, z ∈ principalUnits K r ∧ z ^ d = a := by
  let : HenselianRing 𝒪[K] 𝓂[K] := (localCompleteDVF K).henselianRing
  have hI : (𝓂[K] ^ r : Ideal 𝒪[K]) ≤ 𝓂[K] := by
    simpa only [pow_one] using (Ideal.pow_le_pow_right (I := 𝓂[K]) hr)
  exact HenselianLocalRing.units_pow_root_of_sub_one_mem
    𝒪[K] (𝓂[K] ^ r) hI d hd a ha

end LocalFieldTheory
