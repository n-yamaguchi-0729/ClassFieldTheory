/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdeals
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Tactic.Ring

/-!
# Invertible ideals of nonmaximal orders away from the conductor

An integral ideal of the original order coprime to the conductor is
invertible when it is nonzero. The inverse is the ordinary fractional-ideal
inverse over that order. Upstairs invertibility puts the square of each
conductor element in the product with this inverse; coprimality then puts
one in the product. The smaller order is never assumed to be Dedekind.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

noncomputable section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

private theorem conductor_mul_mem_orderIdeal_inv
    (I : Ideal O) (hI : I ≠ ⊥)
    (hmap : (I.map (orderToRingOfIntegers O).toRingHom :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0)
    {y : K}
    (hy : y ∈ (I.map (orderToRingOfIntegers O).toRingHom :
      FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {c : 𝓞 K} (hc : c ∈ orderConductor O) :
    (c : K) * y ∈ (I : FractionalIdeal O⁰ K)⁻¹ := by
  apply (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)).mpr
  intro z hz
  obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp hz
  have haMap : (a : K) ∈
      (I.map (orderToRingOfIntegers O).toRingHom : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰
      (Ideal.mem_map_of_mem (orderToRingOfIntegers O).toRingHom ha)
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp
    ((FractionalIdeal.mem_inv_iff hmap).mp hy _ haMap)
  refine (FractionalIdeal.mem_one_iff O⁰).mpr ⟨⟨(c : K) * (b : K), hc b⟩, ?_⟩
  change (c : K) * (b : K) = (c : K) * y * (a : K)
  have hb' : (b : K) = y * (a : K) := hb
  exact (congrArg ((c : K) * ·) hb').trans (mul_assoc _ _ _).symm

/-- The square of a conductor element belongs to the product of a nonzero
order ideal with its actual fractional-ideal inverse. -/
theorem orderConductor_sq_mem_ideal_mul_inv
    (I : Ideal O) (hI : I ≠ ⊥) {c : 𝓞 K} (hc : c ∈ orderConductor O) :
    (c : K) ^ 2 ∈ (I : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K)⁻¹ := by
  let J : FractionalIdeal (𝓞 K)⁰ K :=
    I.map (orderToRingOfIntegers O).toRingHom
  have hJ : J ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr
    ((Ideal.map_eq_bot_iff_of_injective
      (Subalgebra.inclusion_injective (finiteSubalgebra_le_ringOfIntegers O))).not.mpr hI)
  let P : FractionalIdeal O⁰ K := (I : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K)⁻¹
  have hprod : ∀ z ∈ J * J⁻¹, (c : K) ^ 2 * z ∈ P := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => (c : K) ^ 2 * z ∈ P) hz ?_ ?_
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
      obtain ⟨b, hb, hba⟩ := orderConductor_mul_mem_ideal_image O I ha c hc
      have hy' := conductor_mul_mem_orderIdeal_inv O I hI hJ hy hc
      have hb' : (b : K) ∈ (I : FractionalIdeal O⁰ K) :=
        FractionalIdeal.mem_coeIdeal_of_mem O⁰ hb
      have hmem := FractionalIdeal.mul_mem_mul hb' hy'
      have hba' : (b : K) = (c : K) * (a : K) :=
        congrArg (fun t : 𝓞 K => (t : K)) hba
      have heq : (c : K) ^ 2 * ((a : K) * y) = (b : K) * ((c : K) * y) := by
        rw [hba']
        ring
      exact heq.symm ▸ hmem
    · intro x y hx hy
      rw [mul_add]
      exact (P : Submodule O K).add_mem hx hy
  have hOne : (1 : K) ∈ J * J⁻¹ := by
    rw [mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one (𝓞 K)⁰
  simpa only [mul_one] using hprod 1 hOne

/-- A nonzero ideal coprime to the conductor is invertible over the original
order, including nonmaximal orders. -/
theorem orderIdeal_isUnit_of_coprime_conductor
    (I : Ideal O) (hI : I ≠ ⊥)
    (hcoprime : I ⊔ (orderConductor O).comap
      (orderToRingOfIntegers O).toRingHom = ⊤) :
    IsUnit (I : FractionalIdeal O⁰ K) := by
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
  apply le_antisymm FractionalIdeal.mul_one_div_le_one
  apply FractionalIdeal.one_le.mpr
  obtain ⟨a, ha, c, hc, hac⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hcoprime)
  let P : FractionalIdeal O⁰ K := (I : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K)⁻¹
  have haP : (a : K) ∈ P :=
    FractionalIdeal.coeIdeal_le_self_mul_inv K I
      (FractionalIdeal.mem_coeIdeal_of_mem O⁰ ha)
  have hcP : (c : K) ^ 2 ∈ P :=
    orderConductor_sq_mem_ideal_mul_inv O I hI hc
  have hsum := (P : Submodule O K).add_mem
    ((P : Submodule O K).smul_mem (1 + c) haP) hcP
  have heq : (1 + c) • (a : K) + (c : K) ^ 2 = 1 := by
    rw [Algebra.smul_def]
    change (1 + (c : K)) * (a : K) + (c : K) ^ 2 = 1
    have hac' : (a : K) + (c : K) = 1 := congrArg (fun x : O => (x : K)) hac
    rw [eq_sub_iff_add_eq.mpr hac']
    ring
  rw [heq] at hsum
  exact hsum

/-- The contraction of a nonzero ideal prime to the conductor is an actual
invertible fractional ideal of the original order. -/
def orderContractedIdealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcoprime : I ⊔ orderConductor O = ⊤) : (FractionalIdeal O⁰ K)ˣ :=
  (orderIdeal_isUnit_of_coprime_conductor O
    (I.comap (orderToRingOfIntegers O).toRingHom)
    (by
      intro hbot
      have hmap := orderIdeal_map_comap_of_coprime_conductor O I hcoprime
      rw [hbot, Ideal.map_bot] at hmap
      exact hI hmap.symm)
    (orderIdeal_comap_sup_conductor_eq_top O I hcoprime)).unit

/-- The bundled invertible ideal has exactly the contracted integral ideal
as its underlying fractional ideal. -/
@[simp]
theorem orderContractedIdealUnit_val (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcoprime : I ⊔ orderConductor O = ⊤) :
    (orderContractedIdealUnit O I hI hcoprime : FractionalIdeal O⁰ K) =
      (I.comap (orderToRingOfIntegers O).toRingHom : FractionalIdeal O⁰ K) :=
  IsUnit.unit_spec _

/-- The class of the actual contracted invertible ideal in Mathlib's class
group of the original order. No Dedekind-only constructor is used. -/
def orderContractedIdealClass (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcoprime : I ⊔ orderConductor O = ⊤) : ClassGroup O :=
  ClassGroup.mk K (orderContractedIdealUnit O I hI hcoprime)

end NumberField
