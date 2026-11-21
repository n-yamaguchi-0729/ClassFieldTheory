/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Generator lifts for finite cyclic quotients -/

@[expose] public section

namespace ClassFieldTheory

/-- A specified generator of a finite cyclic quotient lifts to a generator. -/
theorem exists_cyclicGenerator_lift
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (g : G)
    (hg : Subgroup.zpowers g = ⊤) (y : H) (hy : Subgroup.zpowers y = ⊤) :
    ∃ x : G, f x = y ∧ Subgroup.zpowers x = ⊤ := by
  have hfg : Subgroup.zpowers (f g) = ⊤ := by
    rw [← MonoidHom.map_zpowers, hg, Subgroup.map_top, MonoidHom.range_eq_top.2 hf]
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff y (f g)).mp
    (mem_powers_iff_mem_zpowers.mpr (hfg.symm ▸ Subgroup.mem_top y))
  let d := orderOf g
  let m := orderOf (f g)
  let : NeZero d := ⟨(orderOf_pos g).ne'⟩
  have hmd : m ∣ d := orderOf_map_dvd f g
  have hcop : k.Coprime m := mem_zpowers_pow_iff.mp (by
    rw [hk, hy]
    exact Subgroup.mem_top (f g))
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hmd (ZMod.unitOfCoprime k hcop)
  let n := (u : ZMod d).val
  have hn : (n : ZMod m) = (k : ZMod m) := by
    calc
      (n : ZMod m) = (ZMod.castHom hmd (ZMod m)) (u : ZMod d) := by
        rw [← ZMod.natCast_zmod_val (u : ZMod d), map_natCast]
      _ = (k : ZMod m) := by
        change (ZMod.unitsMap hmd u : ZMod m) = _
        rw [hu, ZMod.coe_unitOfCoprime]
  have hnorder : orderOf (g ^ n) = orderOf g :=
    (ZMod.val_coe_unit_coprime u).symm.orderOf_pow
  refine ⟨g ^ n, ?_, Subgroup.eq_top_of_card_eq _ ?_⟩
  · rw [map_pow, ← hk]
    exact pow_eq_pow_iff_modEq.mpr ((ZMod.natCast_eq_natCast_iff n k m).mp hn)
  · rw [Nat.card_zpowers, hnorder, orderOf_eq_card_of_zpowers_eq_top hg]

/-- A generator in one cyclic quotient has a lift that also generates the other cyclic quotient. -/
theorem exists_diagonal_cyclicGenerator
    {G A B : Type*} [Group G] [Group A] [Group B] [Finite B]
    (a : G →* A) (ha : Function.Surjective a) (b : G →* B) (hb : Function.Surjective b)
    (x : A) (hx : Subgroup.zpowers x = ⊤) (y : B) (hy : Subgroup.zpowers y = ⊤) :
    ∃ g : G, a g = x ∧ Subgroup.zpowers (b g) = ⊤ := by
  let N : Subgroup B := a.ker.map b
  let : N.Normal := (inferInstance : a.ker.Normal).map b hb
  let q := QuotientGroup.mk' N
  have hk : a.ker ≤ (q.comp b).ker := by
    intro g hg
    exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (b g)).2 ⟨g, hg, rfl⟩)
  let c := a.liftOfSurjective ha ⟨q.comp b, hk⟩
  have hc (g : G) : c (a g) = q (b g) :=
    a.liftOfRightInverse_comp_apply (Function.surjInv ha) (Function.rightInverse_surjInv ha)
      ⟨q.comp b, hk⟩ g
  have hcs : Function.Surjective c := by
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N v
    obtain ⟨g, rfl⟩ := hb w
    exact ⟨a g, hc g⟩
  have hcx : Subgroup.zpowers (c x) = ⊤ := by
    rw [← MonoidHom.map_zpowers, hx, Subgroup.map_top, MonoidHom.range_eq_top.2 hcs]
  obtain ⟨z, hz, hzgen⟩ := exists_cyclicGenerator_lift q
    (QuotientGroup.mk'_surjective N) y hy (c x) hcx
  obtain ⟨g, hg⟩ := ha x
  have heq : q (b g) = q z := (hc g).symm.trans ((congrArg c hg).trans hz.symm)
  have hmem : (b g)⁻¹ * z ∈ N := QuotientGroup.eq.1 heq
  obtain ⟨k, hk, hbk⟩ := hmem
  refine ⟨g * k, ?_, ?_⟩
  · rw [map_mul, hg, MonoidHom.mem_ker.mp hk, mul_one]
  · rw [map_mul, hbk, mul_inv_cancel_left]
    exact hzgen

end ClassFieldTheory
