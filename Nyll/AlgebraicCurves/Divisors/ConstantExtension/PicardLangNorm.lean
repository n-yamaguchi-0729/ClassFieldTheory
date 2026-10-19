/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
import Nyll.GaloisCohomology.Cyclic.LangNormKernel
import Mathlib.Tactic.Abel

/-!
# Cyclic Picard norms from the degree sequence and Lang surjectivity

The degree-zero Lang operator supplies all primitives and norm preimages.
A fixed degree-one class identifies the only obstruction to a norm with
integer degree modulo the length of the cyclic norm.
-/

noncomputable section

namespace AlgebraicCurve.H1Gm

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F]

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

omit [HasPrincipalDivisors K F] in
private theorem pic_smul_zsmul (g : SemilinearAut K F) (d : ℤ) (x : Pic K F) :
    g • (d • x) = d • (g • x) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Pic K F) g) d x

/-- Degree sends a cyclic Picard norm to multiplication by the length. -/
theorem degree_cyclic_sum (g : SemilinearAut K F) (n : ℕ) (x : Pic K F) :
    degree K F (∑ i ∈ Finset.range n, g ^ i • x) = n * degree K F x := by
  rw [map_sum]
  simp only [degree_smul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [HasPrincipalDivisors K F] in
private theorem ofPic0_cyclic_sum (g : SemilinearAut K F) (n : ℕ) (x : Pic0 K F) :
    ofPic0 K F (∑ i ∈ Finset.range n, g ^ i • x) =
      ∑ i ∈ Finset.range n, g ^ i • ofPic0 K F x := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => ofPic0_smul (g ^ i) x)

/-- A norm-zero Picard class has a primitive with the same cyclic period. -/
theorem exists_periodic_primitive_of_pic0_lang (g : SemilinearAut K F)
    (hLang : Function.Surjective (fun z : Pic0 K F => g • z - z))
    (n : ℕ) (hn : n ≠ 0) (x : Pic K F)
    (hx : (∑ i ∈ Finset.range n, g ^ i • x) = 0) :
    ∃ y : Pic K F, g ^ n • y = y ∧ g • y - y = x := by
  have hdeg : degree K F x = 0 := by
    have he := congrArg (degree K F) hx
    rw [degree_cyclic_sum, map_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (Int.natCast_ne_zero.mpr hn)
  obtain ⟨z, hz⟩ := (exact_ofPic0_degree K F).ge hdeg
  have hnorm : (∑ i ∈ Finset.range n, g ^ i • z) = 0 := by
    apply ofPic0_injective K F
    rw [ofPic0_cyclic_sum, hz, map_zero, hx]
  obtain ⟨w, hw, he⟩ :=
    CyclicAction.exists_fixed_primitive_of_surjective_sub g hLang n z hnorm
  refine ⟨ofPic0 K F w, ?_, ?_⟩
  · rw [← ofPic0_smul, hw]
  · rw [← ofPic0_smul, ← map_sub, he, hz]

/-- Degree divisibility is the complete norm obstruction when a fixed degree-one class exists. -/
theorem exists_periodic_norm_preimage_iff_of_pic0_lang
    (g : SemilinearAut K F) (n : ℕ)
    (hLang : Function.Surjective (fun z : Pic0 K F => g ^ n • z - z))
    (u : Pic K F) (hu : g • u = u) (hdeg : degree K F u = 1)
    (x : Pic K F) (hx : g • x = x) :
    (∃ y : Pic K F, g ^ n • y = y ∧ ∑ i ∈ Finset.range n, g ^ i • y = x) ↔
      (n : ℤ) ∣ degree K F x := by
  constructor
  · rintro ⟨y, _, hy⟩
    exact ⟨degree K F y, (congrArg (degree K F) hy).symm.trans
      (degree_cyclic_sum g n y)⟩
  · rintro ⟨d, hd⟩
    have hupow (i : ℕ) : g ^ i • u = u := by
      induction i with
      | zero => rw [pow_zero, one_smul]
      | succ i ih => rw [pow_succ', mul_smul, ih, hu]
    let z := x - ((n : ℤ) * d) • u
    have hzdeg : degree K F z = 0 := by
      change degree K F (x - ((n : ℤ) * d) • u) = 0
      rw [map_sub, map_zsmul, hdeg, zsmul_eq_mul, Int.cast_id, mul_one, hd, sub_self]
    have hzfix : g • z = z := by
      change g • (x - ((n : ℤ) * d) • u) = x - ((n : ℤ) * d) • u
      rw [smul_sub, pic_smul_zsmul g, hx, hu]
    obtain ⟨z₀, hz₀⟩ := (exact_ofPic0_degree K F).ge hzdeg
    have hz₀fix : g • z₀ = z₀ := by
      apply ofPic0_injective K F
      rw [ofPic0_smul, hz₀, hzfix]
    obtain ⟨w, hw, hNw⟩ := CyclicAction.exists_fixed_norm_preimage_of_surjective_sub_pow
      g n hLang z₀ hz₀fix
    refine ⟨ofPic0 K F w + d • u, ?_, ?_⟩
    · rw [smul_add, ← ofPic0_smul, hw, pic_smul_zsmul (g ^ n), hupow]
    · have hdu (i : ℕ) : g ^ i • (d • u) = d • u :=
        (pic_smul_zsmul (g ^ i) d u).trans
          (congrArg (fun z : Pic K F => d • z) (hupow i))
      simp only [smul_add, hdu, Finset.sum_add_distrib]
      rw [← ofPic0_cyclic_sum, hNw, hz₀, Finset.sum_const, Finset.card_range]
      change (x - ((n : ℤ) * d) • u) + n • (d • u) = x
      rw [← Nat.cast_smul_eq_nsmul ℤ n (d • u), ← mul_smul, sub_add_cancel]

end AlgebraicCurve.H1Gm
