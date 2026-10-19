/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The total principal-divisor lemmas below are adapted from this Anthropic FLT source:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.Algebra.Group.Action.Units

/-!
# The principal divisor homomorphism and its constant kernel

The actual orders of a nonzero function define an equivariant homomorphism.
Its image is precisely the principal divisors; when constants are the base,
its kernel consists precisely of the base-field units.
-/

noncomputable section

namespace AlgebraicCurve.Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F]

/-- The principal divisor of a unit, as an additive homomorphism. -/
def principalHom : Additive Fˣ →+ Divisor K F where
  toFun x := (HasPrincipalDivisors.exists_divisor (K := K)
    (x.toMul : F) x.toMul.ne_zero).choose
  map_zero' := by
    ext v
    change (HasPrincipalDivisors.exists_divisor (K := K) (1 : F) one_ne_zero).choose v = 0
    rw [(HasPrincipalDivisors.exists_divisor (K := K) (1 : F) one_ne_zero).choose_spec.1]
    exact v.ord_one
  map_add' x y := by
    ext v
    change (HasPrincipalDivisors.exists_divisor (K := K)
      ((x.toMul * y.toMul : Fˣ) : F) (x.toMul * y.toMul).ne_zero).choose v = _
    rw [(HasPrincipalDivisors.exists_divisor (K := K)
      ((x.toMul * y.toMul : Fˣ) : F) (x.toMul * y.toMul).ne_zero).choose_spec.1,
      Finsupp.add_apply]
    change v.ord ((x.toMul : F) * (y.toMul : F)) = _
    rw [v.ord_mul x.toMul.ne_zero y.toMul.ne_zero]
    exact congrArg₂ (· + ·)
      ((HasPrincipalDivisors.exists_divisor (K := K)
        (x.toMul : F) x.toMul.ne_zero).choose_spec.1 v).symm
      ((HasPrincipalDivisors.exists_divisor (K := K)
        (y.toMul : F) y.toMul.ne_zero).choose_spec.1 v).symm

/-- The coefficient of a principal divisor is its actual valuation order. -/
theorem principalHom_apply (x : Additive Fˣ) (v : Place K F) :
    principalHom (K := K) x v = v.ord (x.toMul : F) :=
  (HasPrincipalDivisors.exists_divisor (K := K)
    (x.toMul : F) x.toMul.ne_zero).choose_spec.1 v

/-- Principal divisors have degree zero. -/
theorem degree_principalHom (x : Additive Fˣ) :
    degree (principalHom (K := K) x) = 0 :=
  (HasPrincipalDivisors.exists_divisor (K := K)
    (x.toMul : F) x.toMul.ne_zero).choose_spec.2

open Classical in
/-- A principal divisor of a nonzero function, with the zero divisor assigned to zero. -/
noncomputable def divOf (f : F) : Divisor K F :=
  if hf : f = 0 then 0 else principalHom (K := K) (Additive.ofMul (Units.mk0 f hf))

theorem divOf_apply {f : F} (hf : f ≠ 0) (v : Place K F) :
    divOf f v = v.ord f := by
  rw [divOf, dite_eq_right hf]
  exact principalHom_apply (Additive.ofMul (Units.mk0 f hf)) v

@[simp] theorem divOf_zero : divOf (K := K) (0 : F) = 0 := by
  rw [divOf, dite_eq_left rfl]

theorem degree_divOf (f : F) :
    Divisor.degree (divOf (K := K) f) = 0 := by
  by_cases hf : f = 0
  · subst hf
    rw [divOf_zero, map_zero]
  · rw [divOf, dite_eq_right hf]
    exact degree_principalHom (Additive.ofMul (Units.mk0 f hf))

theorem divOf_mem_principal {f : F} (hf : f ≠ 0) :
    divOf (K := K) f ∈ Divisor.principal :=
  ⟨f, hf, fun v => divOf_apply hf v⟩

theorem isPrincipal_iff_eq_divOf {D : Divisor K F} :
    D.IsPrincipal ↔ ∃ f : F, f ≠ 0 ∧ D = divOf f := by
  constructor
  · rintro ⟨f, hf, hD⟩
    exact ⟨f, hf, Finsupp.ext fun v => by rw [hD v, divOf_apply hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, fun v => divOf_apply hf v⟩

theorem mem_principal_iff_eq_divOf {D : Divisor K F} :
    D ∈ Divisor.principal ↔ ∃ f : F, f ≠ 0 ∧ D = divOf f :=
  isPrincipal_iff_eq_divOf

theorem divOf_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    divOf (K := K) (f * g) = divOf f + divOf g := by
  ext v
  rw [Finsupp.add_apply, divOf_apply (mul_ne_zero hf hg), divOf_apply hf, divOf_apply hg,
    Place.ord_mul _ hf hg]

theorem divOf_inv (f : F) :
    divOf (K := K) f⁻¹ = -divOf f := by
  by_cases hf : f = 0
  · subst hf
    rw [inv_zero, divOf_zero, neg_zero]
  ext v
  rw [Finsupp.neg_apply, divOf_apply (inv_ne_zero hf), divOf_apply hf, Place.ord_inv]

theorem divOf_pow (f : F) (n : ℕ) :
    divOf (K := K) (f ^ n) = (n : ℤ) • divOf f := by
  by_cases hf : f = 0
  · subst hf
    cases n with
    | zero =>
      ext v
      simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
      rw [divOf_apply one_ne_zero, Place.ord_one]
    | succ n => rw [zero_pow (Nat.succ_ne_zero n), divOf_zero, smul_zero]
  induction n with
  | zero =>
    ext v
    simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
    rw [divOf_apply one_ne_zero, Place.ord_one]
  | succ n ih =>
    rw [pow_succ, divOf_mul (pow_ne_zero _ hf) hf, ih]
    rw [Nat.cast_succ, add_smul, one_smul]

theorem divOf_smul_const {c : K} (hc : c ≠ 0) (f : F) :
    divOf (K := K) (c • f) = divOf f := by
  by_cases hf : f = 0
  · subst hf
    rw [smul_zero]
  ext v
  rw [divOf_apply (smul_ne_zero hc hf), divOf_apply hf, Place.ord_smul_of_ne_zero v hc]

theorem divOf_algebraMap (c : K) :
    divOf (K := K) (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, divOf_zero]
  ext v
  rw [divOf_apply ((map_ne_zero (algebraMap K F)).mpr hc), Place.ord_algebraMap]
  rfl

/-- The range of the principal divisor homomorphism is the actual principal subgroup. -/
theorem range_principalHom : (principalHom (K := K) (F := F)).range = principal := by
  ext D
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x.toMul : F), x.toMul.ne_zero, principalHom_apply x⟩
  · rintro ⟨f, hf, hD⟩
    refine ⟨Additive.ofMul (Units.mk0 f hf), ?_⟩
    ext v
    exact (principalHom_apply _ v).trans (hD v).symm

/-- Base-field units have zero principal divisor. -/
theorem principalHom_algebraMap (c : Kˣ) :
    principalHom (K := K) (Additive.ofMul (Units.map (algebraMap K F).toMonoidHom c)) = 0 := by
  ext v
  rw [principalHom_apply]
  exact v.ord_algebraMap (c : K)

/-- When constants are the base, zero principal divisor means a constant unit. -/
theorem principalHom_eq_zero_iff (hC : ConstantsAreBase K F) (x : Additive Fˣ) :
    principalHom (K := K) x = 0 ↔
      ∃ c : Kˣ, Units.map (algebraMap K F).toMonoidHom c = x.toMul := by
  constructor
  · intro hx
    have hmem : (x.toMul : F) ∈ LSpace (0 : Divisor K F) := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro v
      have hv := congrArg (fun D : Divisor K F => D v) hx
      rw [principalHom_apply] at hv
      change v.ord (x.toMul : F) = 0 at hv
      rw [hv, Finsupp.zero_apply, neg_zero]
    rw [hC] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := by
      intro hzero
      apply x.toMul.ne_zero
      rw [← hc, hzero, map_zero]
    refine ⟨Units.mk0 c hc0, ?_⟩
    apply Units.ext
    exact hc
  · rintro ⟨c, hc⟩
    exact congrArg (fun u : Fˣ => principalHom (K := K) (Additive.ofMul u)) hc ▸
      principalHom_algebraMap c

attribute [local instance] Units.mulDistribMulActionRight
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

/-- The principal divisor homomorphism respects actual semilinear automorphisms. -/
theorem principalHom_smul (g : SemilinearAut K F) (x : Additive Fˣ) :
    principalHom (K := K) (Additive.ofMul (g • x.toMul)) = g • principalHom x := by
  ext w
  rw [principalHom_apply, SemilinearAut.divisor_smul_apply, principalHom_apply]
  have h := SemilinearAut.ord_smul g (g⁻¹ • w) (x.toMul : F)
  rw [smul_inv_smul] at h
  exact h

end AlgebraicCurve.Divisor
