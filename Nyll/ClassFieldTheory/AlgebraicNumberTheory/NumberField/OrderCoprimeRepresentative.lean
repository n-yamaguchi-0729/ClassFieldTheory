/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderRayClass
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdealClass
import Nyll.ClassFieldTheory.Algebra.PrincipalFractionalIdeal
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdeals
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderInvertibleIdeal
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Tactic.Choose

/-! # Integral representatives coprime to the conductor of a nonmaximal order -/

@[expose] public section

open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

private theorem finite_maximalIdeals_over_orderConductor :
    Finite {P : Ideal O // P.IsMaximal ∧
      (orderConductor O).comap (orderToRingOfIntegers O).toRingHom ≤ P} := by
  let f : O →+* 𝓞 K := (orderToRingOfIntegers O).toRingHom
  let C := (orderConductor O).comap f
  let q : O →+* O ⧸ C := Ideal.Quotient.mk C
  have : Finite (𝓞 K ⧸ orderConductor O) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (orderConductor_ne_bot O)
  have : Finite (O ⧸ C) := Finite.of_injective
    (Ideal.quotientMap (orderConductor O) f le_rfl)
    (Ideal.quotientMap_injective (I := orderConductor O) (f := f))
  have : Finite (Ideal (O ⧸ C)) :=
    Finite.of_injective (fun I : Ideal (O ⧸ C) => (I : Set (O ⧸ C))) SetLike.coe_injective
  refine Finite.of_injective (fun P : {P : Ideal O // P.IsMaximal ∧ C ≤ P} => P.1.map q) ?_
  intro P Q heq
  apply Subtype.ext
  have h := congrArg (Ideal.comap q) heq
  rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective] at h
  change P.1 ⊔ RingHom.ker (Ideal.Quotient.mk C) =
    Q.1 ⊔ RingHom.ker (Ideal.Quotient.mk C) at h
  rwa [Ideal.mk_ker, sup_eq_left.mpr P.2.2, sup_eq_left.mpr Q.2.2] at h

omit [NumberField K] [Module.Finite ℤ O] [IsFractionRing O K] in
private theorem invertibleFractionalIdeal_mul_inv_val (J : (FractionalIdeal O⁰ K)ˣ) :
    (J : FractionalIdeal O⁰ K) * (J⁻¹ : (FractionalIdeal O⁰ K)ˣ).val = 1 :=
  congrArg (fun U : (FractionalIdeal O⁰ K)ˣ => (U : FractionalIdeal O⁰ K)) (mul_inv_cancel J)

omit [NumberField K] [Module.Finite ℤ O] [IsFractionRing O K] in
private theorem exists_product_outside_maximal (J : (FractionalIdeal O⁰ K)ˣ)
    (P : Ideal O) (hP : P.IsMaximal) :
    ∃ a ∈ (J : FractionalIdeal O⁰ K),
      ∃ b ∈ (J⁻¹ : (FractionalIdeal O⁰ K)ˣ).val,
        ∃ r : O, (r : K) = a * b ∧ r ∉ P := by
  let A : FractionalIdeal O⁰ K := J
  let B : FractionalIdeal O⁰ K := (J⁻¹ : (FractionalIdeal O⁰ K)ˣ).val
  have hprod : A * B = 1 := invertibleFractionalIdeal_mul_inv_val O J
  by_contra h
  have hsubset (z : K) (hz : z ∈ A * B) : ∃ r ∈ P, (r : K) = z := by
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ r ∈ P, (r : K) = z) hz ?_ ?_
    · intro a ha b hb
      have hab : a * b ∈ (1 : FractionalIdeal O⁰ K) :=
        hprod ▸ FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff O⁰).mp hab
      exact ⟨r, by_contra (fun hn => h ⟨a, ha, b, hb, r, hr, hn⟩), hr⟩
    · intro x y hx hy
      obtain ⟨r, hr, hrx⟩ := hx
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨r + s, P.add_mem hr hs, ?_⟩
      change (r : K) + (s : K) = x + y
      rw [hrx, hsy]
  have hone : (1 : K) ∈ A * B := hprod.symm ▸ FractionalIdeal.one_mem_one O⁰
  obtain ⟨r, hr, hr1⟩ := hsubset 1 hone
  have hr' : r = 1 := Subtype.ext hr1
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (hr' ▸ hr))

private theorem exists_conductor_coprime_multiplier (J : (FractionalIdeal O⁰ K)ˣ) :
    ∃ a ∈ (J : FractionalIdeal O⁰ K), a ≠ 0 ∧ ∀ P : Ideal O, P.IsMaximal →
      (orderConductor O).comap (orderToRingOfIntegers O).toRingHom ≤ P →
        ∃ b ∈ (J⁻¹ : (FractionalIdeal O⁰ K)ˣ).val,
          ∃ r : O, (r : K) = a * b ∧ r ∉ P := by
  classical
  let C := (orderConductor O).comap (orderToRingOfIntegers O).toRingHom
  let V := {P : Ideal O // P.IsMaximal ∧ C ≤ P}
  have : Finite V := finite_maximalIdeals_over_orderConductor O
  let : Fintype V := Fintype.ofFinite V
  by_cases hV : Nonempty V
  · let P : V → Ideal O := Subtype.val
    have hcop : Pairwise (fun i j : V => IsCoprime (P i) (P j)) := by
      intro i j hij
      exact Ideal.isCoprime_iff_sup_eq.mpr
        (i.2.1.coprime_of_ne j.2.1 (fun h => hij (Subtype.ext h)))
    let e := Ideal.quotientInfRingEquivPiQuotient P hcop
    let q : O →+* (∀ i, O ⧸ P i) := e.toRingHom.comp (Ideal.Quotient.mk (⨅ i, P i))
    have hq : Function.Surjective q := e.surjective.comp Ideal.Quotient.mk_surjective
    choose w hw using fun i : V => hq (fun j => if i = j then 1 else 0)
    choose a ha b hb r hr using fun i : V => exists_product_outside_maximal O J (P i) i.2.1
    let x : K := ∑ i, (w i : K) * a i
    have hx : x ∈ (J : FractionalIdeal O⁰ K) := by
      apply Submodule.sum_mem ((J : FractionalIdeal O⁰ K) : Submodule O K)
      intro i _
      exact ((J : FractionalIdeal O⁰ K) : Submodule O K).smul_mem (w i) (ha i)
    have hgood (i : V) : ∃ z : O, (z : K) = x * b i ∧ z ∉ P i := by
      have hprod := invertibleFractionalIdeal_mul_inv_val O J
      have hprod' (j : V) : a j * b i ∈ (1 : FractionalIdeal O⁰ K) :=
        hprod ▸ FractionalIdeal.mul_mem_mul (ha j) (hb i)
      choose t ht using fun j : V => (FractionalIdeal.mem_one_iff O⁰).mp (hprod' j)
      let z : O := ∑ j, w j * t j
      have hz : (z : K) = x * b i := by
        change algebraMap O K (∑ j, w j * t j) =
          (∑ j, algebraMap O K (w j) * a j) * b i
        simp only [map_sum, map_mul, ht, Finset.sum_mul, mul_assoc]
      let qi : O →+* O ⧸ P i := Ideal.Quotient.mk (P i)
      have hqi (j : V) : qi (w j) = if j = i then 1 else 0 := congrFun (hw j) i
      have hqz : qi z = qi (t i) := by
        change qi (∑ j, w j * t j) = _
        rw [map_sum, Finset.sum_eq_single i]
        · rw [map_mul, hqi, ite_eq_left rfl, one_mul]
        · intro j _ hji
          rw [map_mul, hqi, ite_eq_right hji, zero_mul]
        · exact fun hi => (hi (Finset.mem_univ i)).elim
      have hti : t i = r i := Subtype.ext ((ht i).trans (hr i).1.symm)
      refine ⟨z, hz, fun hmem => (hr i).2 ?_⟩
      have hzq : qi z = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
      rw [hqz, hti] at hzq
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hzq
    obtain ⟨i⟩ := hV
    have hx0 : x ≠ 0 := by
      intro h0
      obtain ⟨z, hz, hzP⟩ := hgood i
      rw [h0, zero_mul] at hz
      have hz0 : z = 0 := Subtype.ext hz
      exact hzP (hz0.symm ▸ (P i).zero_mem)
    refine ⟨x, hx, hx0, fun Q hQ hC => ?_⟩
    let i : V := ⟨Q, hQ, hC⟩
    exact ⟨b i, hb i, hgood i⟩
  · obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (Units.ne_zero J)
    exact ⟨(x : K), hx, fun h => hx0 (Subtype.ext h), fun P hP hC =>
      (hV ⟨⟨P, hP, hC⟩⟩).elim⟩

/-- Every ideal class of the original order is the class of an actual contracted coprime ideal. -/
theorem orderIdealClassMap_surjective : Function.Surjective (orderIdealClassMap O) := by
  intro c
  refine ClassGroup.induction (K := K) (fun U => ?_) c
  obtain ⟨a, ha, ha0, hgood⟩ := exists_conductor_coprime_multiplier O U⁻¹
  let T : (FractionalIdeal O⁰ K)ˣ := toPrincipalIdeal O K (Units.mk0 a ha0) * U
  have hT : (T : FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ a * U.val := by
    rw [show T = toPrincipalIdeal O K (Units.mk0 a ha0) * U from rfl,
      Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0]
  have hle : (T : FractionalIdeal O⁰ K) ≤ 1 := by
    rw [hT, FractionalIdeal.spanSingleton_mul_le_iff]
    intro b hb
    have hp := invertibleFractionalIdeal_mul_inv_val O U⁻¹
    rw [inv_inv] at hp
    exact hp ▸ FractionalIdeal.mul_mem_mul ha hb
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  let C := (orderConductor O).comap (orderToRingOfIntegers O).toRingHom
  have hcop : I ⊔ C = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hPcontains⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨b, hb, r, hr, hrP⟩ := hgood P hP (le_sup_right.trans hPcontains)
    rw [inv_inv] at hb
    have hrI : (r : K) ∈ (I : FractionalIdeal O⁰ K) := by
      rw [hr, hI, hT]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self O⁰ a) hb
    obtain ⟨s, hs, hsr⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp hrI
    have hsr' : s = r := Subtype.ext hsr
    have hrSup : r ∈ I ⊔ C := (le_sup_left : I ≤ I ⊔ C) (hsr' ▸ hs)
    exact hrP (hPcontains hrSup)
  have hI0 : I ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp (hI.symm ▸ Units.ne_zero T)
  let f : O →+* 𝓞 K := (orderToRingOfIntegers O).toRingHom
  have hmap0 : I.map f ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (Subalgebra.inclusion_injective (finiteSubalgebra_le_ringOfIntegers O))).not.mpr hI0
  let J : orderPrimeToConductorIdeals O :=
    ⟨I.map f, hmap0, orderIdeal_map_sup_conductor_eq_top O I hcop⟩
  have hcontraction : orderContractedIdealUnitMap O J = T := by
    apply Units.ext
    change (orderContractedIdealUnit O J.1 J.2.1 J.2.2 : FractionalIdeal O⁰ K) = _
    rw [orderContractedIdealUnit_val]
    change ((I.map f).comap f : FractionalIdeal O⁰ K) = _
    rw [orderIdeal_comap_map_of_coprime_conductor O I hcop, hI]
  have hprincipal : ClassGroup.mk K (toPrincipalIdeal O K (Units.mk0 a ha0)) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr
      ((FractionalIdeal.isPrincipal_iff _).mpr
        ⟨a, (coe_toPrincipalIdeal (Units.mk0 a ha0)).trans
          (congrArg (FractionalIdeal.spanSingleton O⁰) (Units.val_mk0 ha0))⟩)
  refine ⟨J, ?_⟩
  change ClassGroup.mk K (orderContractedIdealUnitMap O J) = ClassGroup.mk K U
  rw [hcontraction, show T = toPrincipalIdeal O K (Units.mk0 a ha0) * U from rfl,
    map_mul, hprincipal, one_mul]

/-- The actual conductor ray quotient surjects onto the original order class group. -/
theorem orderRayClassToClassGroup_surjective :
    Function.Surjective (orderRayClassToClassGroup O) := by
  intro c
  obtain ⟨I, hI⟩ := orderIdealClassMap_surjective O c
  exact ⟨QuotientGroup.mk' _ (orderIntegralIdealToFractional O I),
    (orderRayClassToClassGroup_integral O I).trans hI⟩

end NumberField
