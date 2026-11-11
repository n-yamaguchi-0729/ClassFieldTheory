/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
public import Mathlib.Tactic.LinearCombination

/-!
# Field-map rigidity from all normalized orders

If the functions without poles are the constants, an order-preserving field
endomorphism preserves every constant ray. Comparing a nonconstant function
with its translate by one fixes that function. Translation by one fixed
nonconstant function then fixes the constants as well. No linearity over the
constant field is assumed.
-/

@[expose] public section

namespace AlgebraicCurve

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- A field automorphism preserving a place's valuation ring preserves its
normalized order. No linearity over the constant field is required. -/
theorem Place.ord_ringEquiv_of_valuationSubring
    (v : Place k F) (σ : F ≃+* F)
    (hmem : ∀ z : F, σ z ∈ v.toValuationSubring ↔ z ∈ v.toValuationSubring)
    (z : F) : v.ord (σ z) = v.ord z := by
  let e : v.toValuationSubring ≃+* v.toValuationSubring :=
    { toFun := fun x => ⟨σ x.val, (hmem x.val).mpr x.property⟩
      invFun := fun y => ⟨σ.symm y.val, (hmem (σ.symm y.val)).mp
        (by rw [σ.apply_symm_apply]; exact y.property)⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.val)
      map_mul' := fun x y => Subtype.ext (σ.map_mul x.val y.val)
      map_add' := fun x y => Subtype.ext (σ.map_add x.val y.val) }
  by_cases hz : z = 0
  · subst z
    rw [map_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hz hπ
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hπ
  let u' : v.toValuationSubringˣ := Units.map e.toMonoidHom u
  have hvalue : σ z = ((u' : v.toValuationSubring) : F) *
      (((e π : v.toValuationSubring) : F) ^ v.ord z) := by
    change σ z = σ (u : v.toValuationSubring) * σ (π : F) ^ v.ord z
    rw [← map_zpow₀, ← map_mul, ← hu]
  rw [hvalue]
  exact v.ord_unit_smul_zpow u' hπ' (v.ord z)

/-- Normalized orders determine a field endomorphism when constants are full
and at least one nonconstant function exists. Constant-field linearity is a
consequence, rather than an additional hypothesis. -/
theorem ringHom_eq_id_of_forall_ord_eq
    (hC : ConstantsAreBase k F) (t : F) (ht : t ∉ (algebraMap k F).range)
    (σ : F →+* F) (hord : ∀ (v : Place k F) (x : F), v.ord (σ x) = v.ord x) :
    σ = RingHom.id F := by
  have hscalar (x : F) (hx : x ≠ 0) : ∃ c : k, σ x = algebraMap k F c * x := by
    have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    have hzero (v : Place k F) : v.ord (σ x * x⁻¹) = 0 := by
      rw [v.ord_mul hσx (inv_ne_zero hx), v.ord_inv, hord, add_neg_cancel]
    have hm : σ x * x⁻¹ ∈ LinearMap.range (Algebra.linearMap k F) := by
      rw [← hC]
      apply mem_lSpace_iff_ord.mpr
      right
      intro v
      rw [Finsupp.zero_apply, neg_zero, hzero]
    obtain ⟨c, hc⟩ := hm
    change algebraMap k F c = σ x * x⁻¹ at hc
    exact ⟨c, by rw [hc, inv_mul_cancel_right₀ hx]⟩
  have hnonconstant (x : F) (hx : x ∉ (algebraMap k F).range) : σ x = x := by
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx ⟨0, map_zero _⟩
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      refine ⟨-1, ?_⟩
      rw [map_neg, map_one]
      exact (eq_neg_of_add_eq_zero_left h).symm
    obtain ⟨c, hc⟩ := hscalar x hx0
    obtain ⟨d, hd⟩ := hscalar (x + 1) hx1
    have hkey : (algebraMap k F d - algebraMap k F c) * x = 1 - algebraMap k F d := by
      rw [map_add, map_one, hc] at hd
      linear_combination (-1 : F) * hd
    by_cases hdc : d = c
    · subst c
      have hd1 : algebraMap k F d = 1 := by
        have hz : (1 : F) - algebraMap k F d = 0 := by
          rw [← hkey, sub_self, zero_mul]
        exact (sub_eq_zero.mp hz).symm
      rw [hc, hd1, one_mul]
    · exfalso
      apply hx
      have hne : algebraMap k F d - algebraMap k F c ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => hdc ((algebraMap k F).injective h)
      refine ⟨(1 - d) / (d - c), ?_⟩
      rw [map_div₀, map_sub, map_sub, map_one, div_eq_iff hne, mul_comm]
      exact hkey.symm
  apply RingHom.ext
  intro x
  change σ x = x
  by_cases hx : x ∈ (algebraMap k F).range
  · obtain ⟨c, rfl⟩ := hx
    have hsum : algebraMap k F c + t ∉ (algebraMap k F).range := by
      rintro ⟨d, hd⟩
      apply ht
      refine ⟨d - c, ?_⟩
      rw [map_sub, hd, add_sub_cancel_left]
    have h := hnonconstant (algebraMap k F c + t) hsum
    rw [map_add, hnonconstant t ht] at h
    exact add_right_cancel h
  · exact hnonconstant x hx

end AlgebraicCurve
