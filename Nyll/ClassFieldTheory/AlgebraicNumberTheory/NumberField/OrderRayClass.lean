/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderFractionalIdealClass
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderPrincipalIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Ring

/-! # The order ideal class map descends through the conductor ray congruence -/

@[expose] public section

open scoped NumberField nonZeroDivisors WithZero
open IsDedekindDomain

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

private def denominatorIdeal (x : K) : Ideal (𝓞 K) where
  carrier := {d | ∃ a : 𝓞 K, (a : K) = (d : K) * x}
  zero_mem' := ⟨0, by
    change (0 : K) = 0 * x
    rw [zero_mul]⟩
  add_mem' {d e} hd he := by
    obtain ⟨a, ha⟩ := hd
    obtain ⟨b, hb⟩ := he
    refine ⟨a + b, ?_⟩
    change (a : K) + (b : K) = ((d : K) + (e : K)) * x
    rw [ha, hb, add_mul]
  smul_mem' c d hd := by
    obtain ⟨a, ha⟩ := hd
    refine ⟨c * a, ?_⟩
    change (c : K) * (a : K) = ((c : K) * (d : K)) * x
    rw [ha, mul_assoc]

private theorem exists_nonzero_mem_denominatorIdeal (x : K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d ∈ denominatorIdeal x := by
  obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj (𝓞 K)⁰ x
  change x * ((d : 𝓞 K) : K) = (a : K) at had
  exact ⟨d, nonZeroDivisors.ne_zero d.property, a, had.symm.trans (mul_comm x _)⟩

private theorem denominatorIdeal_sup_conductor (x : K)
    (hx : ∀ v ∈ (orderConductorModulus O).finitePart.support, v.valuation K x ≤ 1) :
    denominatorIdeal x ⊔ orderConductor O = ⊤ := by
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
  have hc : orderConductor O ≤ P := le_sup_right.trans hle
  have hP0 : P ≠ ⊥ := fun hbot => orderConductor_ne_bot O (le_bot_iff.mp (hbot ▸ hc))
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
  have hv : v ∈ (orderConductorModulus O).finitePart.support :=
    (mem_orderConductorModulus_support_iff O v).mpr hc
  obtain ⟨a, d, had⟩ := v.exists_primeCompl_mul_eq_of_integer x (hx v hv)
  have hd : (d : 𝓞 K) ∈ denominatorIdeal x := by
    change x * ((d : 𝓞 K) : K) = (a : K) at had
    exact ⟨a, had.symm.trans (mul_comm x _)⟩
  have hdSup : (d : 𝓞 K) ∈ denominatorIdeal x ⊔ orderConductor O :=
    (le_sup_left : denominatorIdeal x ≤ denominatorIdeal x ⊔ orderConductor O) hd
  exact d.property (hle hdSup)

private theorem exists_conductor_congruent_denominator (x : K)
    (hx : ∀ v ∈ (orderConductorModulus O).finitePart.support, v.valuation K x ≤ 1) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d - 1 ∈ orderConductor O ∧ d ∈ denominatorIdeal x := by
  obtain ⟨d, hd, c, hc, hsum⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp (denominatorIdeal_sup_conductor O x hx))
  by_cases hd0 : d = 0
  · have hc1 : c = 1 := by simpa only [hd0, zero_add] using hsum
    have htop : orderConductor O = ⊤ := (Ideal.eq_top_iff_one _).mpr (hc1 ▸ hc)
    obtain ⟨d', h0, hmem⟩ := exists_nonzero_mem_denominatorIdeal x
    exact ⟨d', h0, htop.symm ▸ Submodule.mem_top, hmem⟩
  · have hdiff : d - 1 = -c := by rw [← hsum, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact ⟨d, hd0, hdiff.symm ▸ (orderConductor O).neg_mem hc, hd⟩

omit [NumberField K] [Module.Finite ℤ O] [IsFractionRing O K] in
private theorem exists_congruent_element_of_coprime (D : orderPrimeToConductorIdeals O) :
    ∃ d : 𝓞 K, d ∈ D.1 ∧ d ≠ 0 ∧ d - 1 ∈ orderConductor O := by
  obtain ⟨d, hd, c, hc, hsum⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp D.2.2)
  by_cases hd0 : d = 0
  · have hc1 : c = 1 := by simpa only [hd0, zero_add] using hsum
    have htop : orderConductor O = ⊤ := (Ideal.eq_top_iff_one _).mpr (hc1 ▸ hc)
    obtain ⟨d', hd', h0⟩ := (Submodule.ne_bot_iff _).mp D.2.1
    exact ⟨d', hd', h0, htop.symm ▸ Submodule.mem_top⟩
  · have hdiff : d - 1 = -c := by rw [← hsum, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact ⟨d, hd, hd0, hdiff.symm ▸ (orderConductor O).neg_mem hc⟩

private theorem principal_finiteValuation_bounds (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hx : (IdeleGroup.finiteCoordinates (IdeleGroup.principalIdele K x)) v ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n) :
    v.valuation K (x : K) ≤ 1 ∧
      v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  let u : (v.adicCompletion K)ˣ :=
    _root_.IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x)
  change u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v n at hx
  have hunit : u ∈ (v.adicCompletionIntegers K).units :=
    ClassFieldTheory.rayLocalHigherUnitGroup_le_integralUnits v n hx
  have hvalue := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hunit
  change Valued.v ((_root_.IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) :
    (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 at hvalue
  rw [IdeleGroup.finiteComponent_principalIdele, v.valuedAdicCompletion_eq_valuation'] at hvalue
  refine ⟨hvalue.le, ?_⟩
  obtain ⟨y, hy, hy1⟩ :=
    (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_reduction_eq_one v n u).mp hx
  have hyPow := (ClassFieldTheory.rayLocalHigherUnitMap_eq_one_iff v n y).mp hy1
  have hyVal := (HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow K v
    (ClassFieldTheory.rayLocalIntegralValue v y - 1)).mp hyPow
  have hyCoe : (ClassFieldTheory.rayLocalIntegralValue v y : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) := by
    change ((y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = _
    rw [hy]
    exact IdeleGroup.finiteComponent_principalIdele x v
  rw [← v.valuedAdicCompletion_eq_valuation']
  change Valued.v (algebraMap K (v.adicCompletion K) ((x : K) - 1)) ≤ _
  rw [map_sub, map_one]
  change Valued.v ((ClassFieldTheory.rayLocalIntegralValue v y : v.adicCompletion K) - 1) ≤
    WithZero.exp (-(n : ℤ)) at hyVal
  rw [hyCoe] at hyVal
  exact hyVal

private theorem numerator_sub_one_mem_conductor (x : Kˣ) {a d : 𝓞 K}
    (had : (a : K) = (d : K) * (x : K)) (hd : d - 1 ∈ orderConductor O)
    (hx : ∀ v ∈ (orderConductorModulus O).finitePart.support,
      v.valuation K ((x : K) - 1) ≤
        WithZero.exp (-((orderConductorModulus O).finitePart v : ℤ))) :
    a - 1 ∈ orderConductor O := by
  apply (mem_orderConductor_iff_forall_mem_prime_pow O (a - 1)).mpr
  intro v
  by_cases hv : v ∈ (orderConductorModulus O).finitePart.support
  · let n := (orderConductorModulus O).finitePart v
    have hdPow : d - 1 ∈ v.asIdeal ^ n :=
      (mem_orderConductor_iff_forall_mem_prime_pow O (d - 1)).mp hd v
    have hdVal := (v.intValuation_le_pow_iff_mem (d - 1) n).mpr hdPow
    rw [← v.valuation_of_algebraMap (K := K)] at hdVal
    change v.valuation K (algebraMap (𝓞 K) K (d - 1)) ≤ WithZero.exp (-(n : ℤ)) at hdVal
    rw [map_sub, map_one] at hdVal
    apply (v.intValuation_le_pow_iff_mem (a - 1) n).mp
    rw [← v.valuation_of_algebraMap (K := K)]
    change v.valuation K (algebraMap (𝓞 K) K (a - 1)) ≤ WithZero.exp (-(n : ℤ))
    rw [map_sub, map_one]
    have hdIntegral : v.valuation K (d : K) ≤ 1 := v.valuation_le_one d
    have hprod := mul_le_mul' hdIntegral (hx v hv)
    rw [one_mul, ← map_mul] at hprod
    have hsum := (v.valuation K).map_add_le hprod hdVal
    have heq : (a : K) - 1 = (d : K) * ((x : K) - 1) + ((d : K) - 1) := by
      rw [had]
      ring
    exact heq.symm ▸ hsum
  · have hv0 := Finsupp.notMem_support_iff.mp hv
    rw [hv0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

omit [NumberField K] [Module.Finite ℤ O] [IsFractionRing O K] in
private theorem order_mem_of_sub_one_mem_conductor (a : 𝓞 K)
    (ha : a - 1 ∈ orderConductor O) : (a : K) ∈ O := by
  have h := orderConductor_mem_order O ha
  change (a : K) - 1 ∈ O at h
  simpa only [sub_add_cancel] using O.add_mem h O.one_mem

private theorem orderCongruencePrincipalIdeal_fractional
    (a : O) (ha0 : a ≠ 0) (ha : orderToRingOfIntegers O a - 1 ∈ orderConductor O) :
    (orderIntegralIdealToFractional O (orderCongruencePrincipalIdeal O a ha0 ha)).1 =
      toPrincipalIdeal (𝓞 K) K (Units.mk0 (a : K) (fun h => ha0 (Subtype.ext h))) := by
  apply Units.ext
  change (Ideal.span {orderToRingOfIntegers O a} : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [FractionalIdeal.coeIdeal_span_singleton, coe_toPrincipalIdeal, Units.val_mk0]
  exact congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) (orderToRingOfIntegers_coe O a)

private theorem principalIdele_mem_orderConductorRay_of_congruence (a : 𝓞 K)
    (ha0 : (a : K) ≠ 0) (ha : a - 1 ∈ orderConductor O) :
    IdeleGroup.principalIdele K (Units.mk0 (a : K) ha0) ∈
      RayClass.idelePrimeToModulusSubgroup (orderConductorModulus O) := by
  let x : Kˣ := Units.mk0 (a : K) ha0
  let m := orderConductorModulus O
  constructor
  · change (IdeleGroup.infinitePart (IdeleGroup.principalIdele K x)) ∈ m.infiniteCongruenceSubgroup
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro v hv
    change v ∈ (orderConductorModulus O).infinitePart at hv
    rw [orderConductorModulus_infinitePart] at hv
    exact (Finset.notMem_empty v hv).elim
  · intro v hv
    let n := m.finitePart v
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    have haPow : a - 1 ∈ v.asIdeal ^ n :=
      (mem_orderConductor_iff_forall_mem_prime_pow O (a - 1)).mp ha v
    have hnot : a ∉ v.asIdeal := by
      intro hmem
      have hh : a - 1 ∈ v.asIdeal := by
        rw [← pow_one v.asIdeal]
        exact Ideal.pow_le_pow_right hn haPow
      have hone := v.asIdeal.sub_mem hmem hh
      rw [sub_sub_cancel] at hone
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    have hv1 : v.valuation K (a : K) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).mpr hnot
    let u : (v.adicCompletion K)ˣ :=
    _root_.IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x)
    have hu : (u : v.adicCompletion K) = ((a : K) : v.adicCompletion K) :=
      IdeleGroup.finiteComponent_principalIdele x v
    have hu' : u ∈ (v.adicCompletionIntegers K).units :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
        change Valued.v (u : v.adicCompletion K) = 1
        rw [hu, v.valuedAdicCompletion_eq_valuation', hv1])
    let y : (v.adicCompletionIntegers K).units := ⟨u, hu'⟩
    change u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v n
    apply (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_reduction_eq_one v n u).mpr
    refine ⟨y, rfl, (ClassFieldTheory.rayLocalHigherUnitMap_eq_one_iff v n y).mpr ?_⟩
    apply (HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow K v
      (ClassFieldTheory.rayLocalIntegralValue v y - 1)).mpr
    change Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))
    rw [hu]
    change Valued.v (algebraMap K (v.adicCompletion K) (a : K) - 1) ≤ _
    rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub]
    have hval := v.valuedAdicCompletion_eq_valuation' (K := K) ((a : K) - 1)
    change Valued.v (algebraMap K (v.adicCompletion K) ((a : K) - 1)) =
      v.valuation K ((a : K) - 1) at hval
    rw [hval]
    change v.valuation K (algebraMap (𝓞 K) K a - 1) ≤ _
    rw [← map_one (algebraMap (𝓞 K) K), ← map_sub, v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem (a - 1) n).mpr haPow

private theorem orderCongruencePrincipalIdeal_mem_rayPrincipal
    (a : O) (ha0 : a ≠ 0) (ha : orderToRingOfIntegers O a - 1 ∈ orderConductor O) :
    orderIntegralIdealToFractional O (orderCongruencePrincipalIdeal O a ha0 ha) ∈
      RayClass.principalRayIdealSubgroup (orderConductorModulus O) := by
  apply (RayClass.mem_principalRayIdealSubgroup_iff (orderConductorModulus O) _).mpr
  have haK : (a : K) ≠ 0 := fun h => ha0 (Subtype.ext h)
  refine ⟨Units.mk0 (a : K) haK, ?_, (orderCongruencePrincipalIdeal_fractional O a ha0 ha).symm⟩
  exact principalIdele_mem_orderConductorRay_of_congruence O (orderToRingOfIntegers O a) haK ha

/-- Every conductor ray-principal ideal has trivial class in the original order. -/
theorem principalRayIdealSubgroup_le_orderFractionalIdealClassMap_ker :
    RayClass.principalRayIdealSubgroup (orderConductorModulus O) ≤
      (orderFractionalIdealClassMap O).ker := by
  intro I hI
  obtain ⟨x, hx, hxI⟩ :=
    (RayClass.mem_principalRayIdealSubgroup_iff (orderConductorModulus O) I).mp hI
  have hlocal (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∈ (orderConductorModulus O).finitePart.support) :=
    principal_finiteValuation_bounds x v _ (hx.2 v hv)
  obtain ⟨d, hd0, hd, a, ha⟩ :=
    exists_conductor_congruent_denominator O (x : K) (fun v hv => (hlocal v hv).1)
  have haC := numerator_sub_one_mem_conductor O x ha hd (fun v hv => (hlocal v hv).2)
  let aO : O := ⟨(a : K), order_mem_of_sub_one_mem_conductor O a haC⟩
  let dO : O := ⟨(d : K), order_mem_of_sub_one_mem_conductor O d hd⟩
  have hdK : (d : K) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have haK : (a : K) ≠ 0 := by
    rw [ha]
    exact mul_ne_zero hdK x.ne_zero
  have haO0 : aO ≠ 0 := fun h => haK (congrArg (fun z : O => (z : K)) h)
  have hdO0 : dO ≠ 0 := fun h => hdK (congrArg (fun z : O => (z : K)) h)
  have haO : orderToRingOfIntegers O aO - 1 ∈ orderConductor O := haC
  have hdO : orderToRingOfIntegers O dO - 1 ∈ orderConductor O := hd
  let A := orderCongruencePrincipalIdeal O aO haO0 haO
  let D := orderCongruencePrincipalIdeal O dO hdO0 hdO
  have hprod : orderIntegralIdealToFractional O A = orderIntegralIdealToFractional O D * I := by
    apply Subtype.ext
    change (orderIntegralIdealToFractional O A).1 = (orderIntegralIdealToFractional O D).1 * I.1
    rw [orderCongruencePrincipalIdeal_fractional O aO haO0 haO,
      orderCongruencePrincipalIdeal_fractional O dO hdO0 hdO, ← hxI, ← map_mul]
    exact congrArg (toPrincipalIdeal (𝓞 K) K) (Units.ext ha)
  have h := congrArg (orderFractionalIdealClassMap O) hprod
  rw [map_mul, orderFractionalIdealClassMap_integral, orderFractionalIdealClassMap_integral] at h
  have hA := orderIdealClassMap_orderCongruencePrincipalIdeal O aO haO0 haO
  have hD := orderIdealClassMap_orderCongruencePrincipalIdeal O dO hdO0 hdO
  change orderIdealClassMap O A = 1 at hA
  change orderIdealClassMap O D = 1 at hD
  rw [hA, hD, one_mul] at h
  exact MonoidHom.mem_ker.mpr h.symm

/-- The arithmetic quotient from the conductor ray group to the ideal class group of the order. -/
noncomputable def orderRayClassToClassGroup :
    RayClass.IdealRayClassGroup (orderConductorModulus O) →* ClassGroup O :=
  QuotientGroup.lift (RayClass.principalRayIdealSubgroup (orderConductorModulus O))
    (orderFractionalIdealClassMap O)
    (principalRayIdealSubgroup_le_orderFractionalIdealClassMap_ker O)

@[simp]
theorem orderRayClassToClassGroup_integral (I : orderPrimeToConductorIdeals O) :
    orderRayClassToClassGroup O
      (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup (orderConductorModulus O))
        (orderIntegralIdealToFractional O I)) = orderIdealClassMap O I := by
  exact orderFractionalIdealClassMap_integral O I

/-- Every conductor ray class has an integral representative coprime to the conductor. -/
theorem exists_orderIntegralIdeal_rayClass
    (c : RayClass.IdealRayClassGroup (orderConductorModulus O)) :
    ∃ J : orderPrimeToConductorIdeals O,
      QuotientGroup.mk' (RayClass.principalRayIdealSubgroup (orderConductorModulus O))
        (orderIntegralIdealToFractional O J) = c := by
  let m := orderConductorModulus O
  let q := QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m)
  obtain ⟨I, hI⟩ := QuotientGroup.mk'_surjective _ c
  obtain ⟨A, D, hAD⟩ := exists_orderIntegralIdeals_fractional_mul O I
  obtain ⟨d, hd, hd0, hdC⟩ := exists_congruent_element_of_coprime O D
  let dO : O := ⟨(d : K), order_mem_of_sub_one_mem_conductor O d hdC⟩
  have hdO0 : dO ≠ 0 := fun h => hd0 (Subtype.ext (congrArg (fun z : O => (z : K)) h))
  have hdO : orderToRingOfIntegers O dO - 1 ∈ orderConductor O := hdC
  let P := orderCongruencePrincipalIdeal O dO hdO0 hdO
  have hP : P.1 ≤ D.1 := (Ideal.span_singleton_le_iff_mem D.1).mpr hd
  let T := I * orderIntegralIdealToFractional O P
  let val : RayClass.primeToModulusIdeals m → FractionalIdeal (𝓞 K)⁰ K :=
    fun J => (J.1 : FractionalIdeal (𝓞 K)⁰ K)
  have hle : val T ≤ 1 := calc
    val T = val I * (P.1 : FractionalIdeal (𝓞 K)⁰ K) := rfl
    _ ≤ val I * (D.1 : FractionalIdeal (𝓞 K)⁰ K) :=
      mul_le_mul_right ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hP) (val I)
    _ = val (orderIntegralIdealToFractional O A) := (congrArg val hAD).symm
    _ ≤ 1 := FractionalIdeal.coeIdeal_le_one
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hT0 : val T ≠ 0 := Units.ne_zero T.1
  have hJ0 : J ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp (hJ.symm ▸ hT0)
  have hcount (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
      FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    rw [hJ]
    exact T.2 v hv
  let J' : orderPrimeToConductorIdeals O :=
    ⟨J, hJ0, (orderIdeal_coprime_conductor_iff O J hJ0).mpr hcount⟩
  have hT : orderIntegralIdealToFractional O J' = T := Subtype.ext (Units.ext hJ)
  have hPq : q (orderIntegralIdealToFractional O P) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (orderCongruencePrincipalIdeal_mem_rayPrincipal O dO hdO0 hdO)
  refine ⟨J', ?_⟩
  change q (orderIntegralIdealToFractional O J') = c
  rw [hT, show T = I * orderIntegralIdealToFractional O P from rfl, map_mul, hPq]
  exact (mul_one (q I)).trans hI

/-- The exact Picard kernel consists of classes represented by coprime principal ideals with
generator in the original order. -/
theorem orderRayClassToClassGroup_eq_one_iff
    (c : RayClass.IdealRayClassGroup (orderConductorModulus O)) :
    orderRayClassToClassGroup O c = 1 ↔
      ∃ (J : orderPrimeToConductorIdeals O) (a : O),
        QuotientGroup.mk' (RayClass.principalRayIdealSubgroup (orderConductorModulus O))
          (orderIntegralIdealToFractional O J) = c ∧
        J.1 = Ideal.span ({orderToRingOfIntegers O a} : Set (𝓞 K)) := by
  constructor
  · intro hc
    obtain ⟨J, rfl⟩ := exists_orderIntegralIdeal_rayClass O c
    rw [orderRayClassToClassGroup_integral] at hc
    obtain ⟨a, ha⟩ := (orderIdealClassMap_eq_one_iff O J).mp hc
    exact ⟨J, a, rfl, ha⟩
  · rintro ⟨J, a, rfl, ha⟩
    rw [orderRayClassToClassGroup_integral]
    exact (orderIdealClassMap_eq_one_iff O J).mpr ⟨a, ha⟩

/-- With unit conductor every principal representative in the order is ray-principal. -/
theorem orderRayClassToClassGroup_injective_of_conductor_eq_top
    (h : orderConductor O = ⊤) : Function.Injective (orderRayClassToClassGroup O) := by
  apply (injective_iff_map_eq_one (orderRayClassToClassGroup O)).mpr
  intro c hc
  obtain ⟨J, a, rfl, hJ⟩ := (orderRayClassToClassGroup_eq_one_iff O c).mp hc
  have ha0 : a ≠ 0 := by
    intro hzero
    apply J.2.1
    rw [hJ, hzero, map_zero, Ideal.span_singleton_eq_bot]
  have ha : orderToRingOfIntegers O a - 1 ∈ orderConductor O := h.symm ▸ Submodule.mem_top
  have hJ' : J = orderCongruencePrincipalIdeal O a ha0 ha := Subtype.ext hJ
  rw [hJ']
  exact (QuotientGroup.eq_one_iff _).mpr (orderCongruencePrincipalIdeal_mem_rayPrincipal O a ha0 ha)

end NumberField
