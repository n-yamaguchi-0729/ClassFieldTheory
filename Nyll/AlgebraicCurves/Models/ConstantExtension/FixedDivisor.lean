/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.FunctionPeriod
import Nyll.GaloisCohomology.FieldTheory.PeriodicHilbert90
import Nyll.GaloisCohomology.Cyclic.MultiplicativeLangNorm
import Mathlib.Tactic.Abel

/-!
# Fixed geometric divisors representing Frobenius-invariant classes

Finite periods of the actual divisor and rational function give a cyclic norm
obstruction in the constants. Multiplicative Lang removes that obstruction;
Hilbert 90 in the actual periodic subfield then supplies the principal correction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve CyclicAction

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M : CurveModel Ω F) {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c] [IsSeparated c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

local notation "φ" =>
  M.constantSemilinearAction c e he (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Every actual Frobenius-invariant geometric divisor class has a fixed divisor representative. -/
theorem exists_constantFrobenius_fixed_divisor (D : Divisor Ω F)
    (hD : (φ • D - D).IsPrincipal) :
    ∃ E : Divisor Ω F, (D - E).IsPrincipal ∧ Divisor.degree E = Divisor.degree D ∧ φ • E = E := by
  let unitAction : MulDistribMulAction (SemilinearAut Ω F) Fˣ := Units.mulDistribMulActionRight
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  let ι : Ωˣ →* Fˣ := Units.map (algebraMap Ω F).toMonoidHom
  have hι (i : ℕ) (a : Ωˣ) : φ ^ i • ι a = ι (σ ^ i • a) := by
    apply Units.ext
    change φ ^ i • algebraMap Ω F (a : Ω) = algebraMap Ω F ((σ ^ i) (a : Ω))
    rw [← map_pow, SemilinearAut.smul_algebraMap, M.constantSemilinearAction_baseAut]
    rfl
  obtain ⟨x, hx⟩ := (show φ • D - D ∈ (Divisor.principalHom (K := Ω) (F := F)).range by
    rw [Divisor.range_principalHom]
    exact hD)
  let u := x.toMul
  obtain ⟨n, hn, hDn⟩ := M.exists_constantFrobenius_divisor_period c e he D
  obtain ⟨m, hm, hum⟩ := M.exists_constantFrobenius_function_period c e he (u : F)
  let r := n * m
  have hr : r ≠ 0 := mul_ne_zero hn hm
  have hDr : φ ^ r • D = D := periodicSubgroup_le_mul φ n m hDn
  have hur : φ ^ r • u = u := by
    apply Units.ext
    change φ ^ (n * m) • (u : F) = (u : F)
    rw [Nat.mul_comm]
    exact periodicSubgroup_le_mul φ m n hum
  let N := ∏ i ∈ Finset.range r, φ ^ i • u
  have hNzero : Divisor.principalHom (K := Ω) (Additive.ofMul N) = 0 := by
    change Divisor.principalHom (K := Ω)
      (Additive.ofMul (∏ i ∈ Finset.range r, φ ^ i • u)) = 0
    rw [ofMul_prod, map_sum]
    have hp (i : ℕ) : Divisor.principalHom (K := Ω) (Additive.ofMul (φ ^ i • u)) =
        φ ^ i • (φ • D - D) :=
      (Divisor.principalHom_smul (φ ^ i) x).trans (congrArg (fun E => φ ^ i • E) hx)
    simp only [hp]
    rw [sum_range_smul_sub, hDr, sub_self]
  have hNfixed : φ • N = N := by
    apply div_eq_one.mp
    exact (smul_prod_range_div φ r u).trans (by rw [hur, div_self'])
  obtain ⟨p⟩ := M.nonempty_rationalPoint
  let v := M.pointEquivPlace p
  have hC : ConstantsAreBase Ω F := constantsAreBase_of_exists_isRational v
    ((Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v))
    (by rw [IsCurveOver.deg_eq_one_of_isAlgClosed]; exact Nat.one_ne_zero)
  obtain ⟨z, hz⟩ := (Divisor.principalHom_eq_zero_iff hC (Additive.ofMul N)).mp hNzero
  change ι z = N at hz
  have hzfix : σ • z = z := by
    apply Units.map_injective (algebraMap Ω F).injective
    change ι (σ • z) = ι z
    have h := hι 1 z
    simp only [pow_one] at h
    rw [← h, hz, hNfixed]
  obtain ⟨a, ha, hNa⟩ := exists_periodic_norm_preimage_of_surjective_div_pow σ r
    (fun z => FiniteField.exists_unit_frobenius_pow_div k Ω r hr z) z hzfix
  have hNaF : (∏ i ∈ Finset.range r, φ ^ i • ι a) = N := by
    simp only [hι, ← map_prod]
    rw [hNa, hz]
  let t := u / ι a
  have htperiod : φ ^ r • t = t := by
    change φ ^ r • (u / ι a) = u / ι a
    rw [smul_div', hur, hι, ha]
  have htN : (∏ i ∈ Finset.range r, φ ^ i • t) = 1 := by
    change (∏ i ∈ Finset.range r, φ ^ i • (u / ι a)) = 1
    simp only [smul_div', Finset.prod_div_distrib]
    rw [hNaF]
    exact div_self' N
  let τ := SemilinearAut.toRingAut φ
  have hτ (i : ℕ) (b : F) : (τ ^ i) b = φ ^ i • b := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', RingAut.mul_apply, pow_succ', mul_smul, ih]; rfl
  have htfield : (τ ^ r) (t : F) = (t : F) := by
    rw [hτ]
    exact congrArg Units.val htperiod
  have hNtfield : (∏ i ∈ Finset.range r, (τ ^ i) (t : F)) = 1 := by
    have h := congrArg Units.val htN
    rw [Units.coe_prod] at h
    simpa only [hτ, Units.coe_smul, Units.val_one] using h
  obtain ⟨y, hy0, -, hy⟩ := FiniteField.exists_periodic_frobenius_coboundary τ
    (fun b => SemilinearAut.commutes φ b) r hr (t : F) t.ne_zero htfield hNtfield
  let yu := Units.mk0 y hy0
  have hyu : (φ • yu) / yu = t := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    exact hy
  let P := Divisor.principalHom (K := Ω) (Additive.ofMul yu)
  have hP : φ • P - P = Divisor.principalHom x := by
    rw [← Divisor.principalHom_smul φ (Additive.ofMul yu), ← map_sub]
    change Divisor.principalHom (K := Ω) (Additive.ofMul ((φ • yu) / yu)) = _
    rw [hyu]
    change Divisor.principalHom (K := Ω) (x - Additive.ofMul (ι a)) = _
    rw [map_sub, Divisor.principalHom_algebraMap, sub_zero]
  refine ⟨D - P, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    apply Divisor.mem_principal.mp
    rw [← Divisor.range_principalHom]
    exact ⟨Additive.ofMul yu, rfl⟩
  · rw [map_sub, Divisor.degree_principalHom, sub_zero]
  · apply sub_eq_zero.mp
    calc
      φ • (D - P) - (D - P) = (φ • D - D) - (φ • P - P) := by
        rw [smul_sub]
        abel
      _ = 0 := by rw [hP, hx, sub_self]

end AlgebraicCurve.CurveModel
