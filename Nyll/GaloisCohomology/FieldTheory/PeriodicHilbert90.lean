/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.FiniteActionHilbert90
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusPeriodicField
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Hilbert 90 inside an actual periodic subfield

Restriction to the periodic subfield gives a finite faithful cyclic field
action. Its group norm is compared with the original length-n product.
For arithmetic Frobenius, the exact order is supplied by the finite constants.
-/

noncomputable section

namespace RingAut

open CyclicCohomology.ProfiniteCohomology.Herbrand

attribute [local instance] Units.mulDistribMulActionRight

variable {F : Type*} [Field F]

/-- Length-n norm-one elements have periodic primitives when the restriction has order n. -/
theorem exists_periodic_coboundary (σ : RingAut F) (n : ℕ) (hn : n ≠ 0)
    (horder : orderOf (periodicAut σ n) = n) (x : F) (hx : x ≠ 0)
    (hperiod : (σ ^ n) x = x) (hN : ∏ i ∈ Finset.range n, (σ ^ i) x = 1) :
    ∃ y : F, y ≠ 0 ∧ (σ ^ n) y = y ∧ σ y / y = x := by
  let L := periodicSubfield σ n
  let α := periodicAut σ n
  let H := Subgroup.zpowers α
  have hα : IsOfFinOrder α :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, periodicAut_pow_period σ n⟩
  have : Finite H := finite_zpowers.mpr hα
  let : Fintype H := Fintype.ofFinite H
  have hfaithful : FaithfulSMul H L := ⟨fun {g h} he => Subtype.ext (RingEquiv.ext he)⟩
  let δ : H := ⟨α, Subgroup.mem_zpowers α⟩
  have hδ (g : H) : g ∈ Subgroup.zpowers δ := by
    obtain ⟨i, hi⟩ := g.property
    exact ⟨i, Subtype.ext hi⟩
  let u : Lˣ := Units.mk0 (⟨x, hperiod⟩ : L) (fun h => hx (congrArg Subtype.val h))
  have hnorm : tateNorm H Lˣ u = 1 := by
    apply Units.ext
    change ((∏ g : H, g • u : Lˣ) : L) = 1
    rw [Units.coe_prod]
    apply L.subtype.injective
    rw [map_prod, map_one]
    calc
      (∏ g : H, L.subtype ((g • u : Lˣ) : L)) =
          ∏ i : Fin (orderOf α), (σ ^ i.val) x := by
        apply (Fintype.prod_equiv (finEquivZPowers hα) _ _ ?_).symm
        intro i
        exact (periodicAut_pow_coe σ n i.val (u : L)).symm
      _ = ∏ i ∈ Finset.range (orderOf α), (σ ^ i) x :=
        Fin.prod_univ_eq_prod_range (fun i : ℕ => (σ ^ i) x) (orderOf α)
      _ = 1 := by rw [horder]; exact hN
  obtain ⟨y, hy⟩ := CyclicCohomology.exists_unit_coboundary_of_finite_action_norm_eq_one
    (G := H) (L := L) δ hδ u hnorm
  refine ⟨((y : L) : F), ?_, (y : L).property, ?_⟩
  · exact (map_ne_zero_iff L.subtype L.subtype.injective).mpr y.ne_zero
  · have h := congrArg Units.val hy
    rw [Units.val_div_eq_div_val] at h
    have he := congrArg L.subtype h
    rw [map_div₀] at he
    exact he

end RingAut

namespace FiniteField

/-- Hilbert 90 for actual Frobenius-periodic rational functions over algebraic constants. -/
theorem exists_periodic_frobenius_coboundary
    {k Ω F : Type*} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F]
    (σ : RingAut F) (hσ : ∀ a : Ω, σ (algebraMap Ω F a) =
      algebraMap Ω F (frobeniusAlgEquivOfAlgebraic k Ω a))
    (n : ℕ) (hn : n ≠ 0) (x : F) (hx : x ≠ 0)
    (hperiod : (σ ^ n) x = x) (hN : ∏ i ∈ Finset.range n, (σ ^ i) x = 1) :
    ∃ y : F, y ≠ 0 ∧ (σ ^ n) y = y ∧ σ y / y = x :=
  RingAut.exists_periodic_coboundary σ n hn
    (orderOf_periodicAut_of_frobenius σ hσ n hn) x hx hperiod hN

end FiniteField
