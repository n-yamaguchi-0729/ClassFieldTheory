/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderConductorModulus
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderIdealClass
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
import Lean.Elab.Tactic.Omega

/-! # Contraction of fractional ideals away from an order conductor -/

@[expose] public section

open scoped NumberField nonZeroDivisors
open ClassFieldTheory
open IsDedekindDomain

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

/-- A nonzero integral ideal coprime to the conductor is prime to the full conductor modulus. -/
noncomputable def orderIntegralIdealToFractional :
    orderPrimeToConductorIdeals O →* RayClass.primeToModulusIdeals (orderConductorModulus O) where
  toFun I :=
    ⟨FractionalIdeal.mk0 K ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩,
      (orderIdeal_coprime_conductor_iff O I.1 I.2.1).mp I.2.2⟩
  map_one' := by
    apply Subtype.ext
    exact (FractionalIdeal.mk0 K).map_one
  map_mul' I J := by
    apply Subtype.ext
    exact (FractionalIdeal.mk0 K).map_mul
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩
      ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr J.2.1⟩

/-- A prime away from the conductor modulus is coprime to the actual conductor ideal. -/
theorem orderPrime_coprime_conductor (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (orderConductorModulus O).finitePart.support) :
    v.asIdeal ⊔ orderConductor O = ⊤ := by
  by_contra h
  have heq := v.isMaximal.eq_of_le h le_sup_left
  exact hv ((mem_orderConductorModulus_support_iff O v).mpr (le_sup_right.trans_eq heq.symm))

/-- The prime ideal when it is coprime to the conductor, and the unit ideal otherwise. -/
noncomputable def conductorCoprimeIntegralPrime (v : HeightOneSpectrum (𝓞 K)) :
    orderPrimeToConductorIdeals O := by
  classical
  exact if hv : v ∉ (orderConductorModulus O).finitePart.support then
    ⟨v.asIdeal, v.ne_bot, orderPrime_coprime_conductor O v hv⟩ else 1

private theorem orderIntegralIdealToFractional_conductorCoprimeIntegralPrime
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ (orderConductorModulus O).finitePart.support) :
    (orderIntegralIdealToFractional O (conductorCoprimeIntegralPrime O v) :
      NumberFieldFractionalIdealGroup K) =
      finitePrimeFractionalIdeal v := by
  classical
  unfold conductorCoprimeIntegralPrime
  rw [dite_eq_left hv]
  apply Units.ext
  rfl

/-- Clearing the negative exponents of a prime-to-conductor fractional ideal uses
two integral ideals coprime to the same conductor. -/
theorem exists_orderIntegralIdeals_fractional_mul
    (I : RayClass.primeToModulusIdeals (orderConductorModulus O)) :
    ∃ A D : orderPrimeToConductorIdeals O,
      orderIntegralIdealToFractional O A = I * orderIntegralIdealToFractional O D := by
  classical
  let f : orderPrimeToConductorIdeals O →* NumberFieldFractionalIdealGroup K :=
    (RayClass.primeToModulusIdeals (orderConductorModulus O)).subtype.comp
      (orderIntegralIdealToFractional O)
  let e := NumberFieldFractionalIdealGroup.countVector I.1
  let A := e.prod fun v n => conductorCoprimeIntegralPrime O v ^ n.toNat
  let D := e.prod fun v n => conductorCoprimeIntegralPrime O v ^ (-n).toNat
  have hprime (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ e.support) :
      f (conductorCoprimeIntegralPrime O v) = finitePrimeFractionalIdeal v := by
    have hv' : v ∉ (orderConductorModulus O).finitePart.support := fun hm =>
      (Finsupp.mem_support_iff.mp hv) (I.2 v hm)
    exact orderIntegralIdealToFractional_conductorCoprimeIntegralPrime O v hv'
  have he : f A * (f D)⁻¹ =
      NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) := by
    change f (e.prod _) * (f (e.prod _))⁻¹ = e.prod (fun v n => finitePrimeFractionalIdeal v ^ n)
    simp only [map_finsuppProd, map_pow, ← Finsupp.prod_inv, ← Finsupp.prod_mul]
    apply Finsupp.prod_congr
    intro v hv
    rw [hprime v hv]
    let n := e v
    change finitePrimeFractionalIdeal v ^ n.toNat *
      (finitePrimeFractionalIdeal v ^ (-n).toNat)⁻¹ = finitePrimeFractionalIdeal v ^ n
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  have hI : NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) = I.1 :=
    (NumberFieldFractionalIdealGroup.factorizationEquiv (K := K)).apply_symm_apply I.1
  refine ⟨A, D, Subtype.ext ?_⟩
  change f A = I.1 * f D
  rw [← hI, ← he, mul_assoc, inv_mul_cancel, mul_one]

/-- The invertible contraction of a signed power of a prime away from the conductor. -/
noncomputable def conductorPrimePowerContraction (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* (FractionalIdeal O⁰ K)ˣ :=
  MonoidHom.mk'
    (fun n => orderContractedIdealUnitMap O (conductorCoprimeIntegralPrime O v) ^ n.toAdd)
    (fun a b => by rw [toAdd_mul, zpow_add])

/-- Contract each prime factor with its signed exponent to obtain an invertible fractional ideal
of the original order. The omitted factors have exponent zero by the ray support condition. -/
noncomputable def orderFractionalContraction :
    RayClass.primeToModulusIdeals (orderConductorModulus O) →* (FractionalIdeal O⁰ K)ˣ :=
  MonoidHom.mk' (fun I => (NumberFieldFractionalIdealGroup.countVector I.1).prod
    fun v n => conductorPrimePowerContraction O v (Multiplicative.ofAdd n))
    (fun I J => by
      change (NumberFieldFractionalIdealGroup.countVector (I.1 * J.1)).prod _ = _
      have hcount : NumberFieldFractionalIdealGroup.countVector (I.1 * J.1) =
          NumberFieldFractionalIdealGroup.countVector I.1 +
            NumberFieldFractionalIdealGroup.countVector J.1 := by
        simpa only [toAdd_mul, NumberFieldFractionalIdealGroup.factorizationEquiv_symm_toAdd] using
          congrArg Multiplicative.toAdd
            ((NumberFieldFractionalIdealGroup.factorizationEquiv (K := K)).symm.map_mul I.1 J.1)
      rw [hcount]
      exact Finsupp.prod_hom_add_index (conductorPrimePowerContraction O))

/-- Contraction on the fractional group agrees with the actual invertible contraction
of integral ideals. -/
theorem orderFractionalContraction_integral (I : orderPrimeToConductorIdeals O) :
    orderFractionalContraction O (orderIntegralIdealToFractional O I) =
      orderContractedIdealUnitMap O I := by
  classical
  let f : orderPrimeToConductorIdeals O →* NumberFieldFractionalIdealGroup K :=
    (RayClass.primeToModulusIdeals (orderConductorModulus O)).subtype.comp
      (orderIntegralIdealToFractional O)
  let e := NumberFieldFractionalIdealGroup.countVector (f I)
  let J := e.prod fun v n => conductorCoprimeIntegralPrime O v ^ n.toNat
  have hcount (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ e v :=
    FractionalIdeal.count_coeIdeal_nonneg K v I.1
  have hprime (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ e.support) :
      f (conductorCoprimeIntegralPrime O v) = finitePrimeFractionalIdeal v := by
    have hv' : v ∉ (orderConductorModulus O).finitePart.support := fun hm =>
      (Finsupp.mem_support_iff.mp hv) ((orderIntegralIdealToFractional O I).2 v hm)
    exact orderIntegralIdealToFractional_conductorCoprimeIntegralPrime O v hv'
  have hJI : J = I := by
    have hval : f J = f I := calc
      f J = e.prod (fun v n => f (conductorCoprimeIntegralPrime O v) ^ n.toNat) := by
        change f (e.prod _) = _
        simp only [map_finsuppProd, map_pow]
      _ = NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) := by
        change _ = e.prod (fun v n => finitePrimeFractionalIdeal v ^ n)
        apply Finsupp.prod_congr
        intro v hv
        rw [hprime v hv, ← zpow_natCast, Int.toNat_of_nonneg (hcount v)]
      _ = f I :=
        (NumberFieldFractionalIdealGroup.factorizationEquiv (K := K)).apply_symm_apply (f I)
    apply Subtype.ext
    exact FractionalIdeal.coeIdeal_injective
      (congrArg (fun U : NumberFieldFractionalIdealGroup K => (U : FractionalIdeal (𝓞 K)⁰ K)) hval)
  calc
    orderFractionalContraction O (orderIntegralIdealToFractional O I) =
        orderContractedIdealUnitMap O J := by
      change (e.prod fun v n => (orderContractedIdealUnitMap O
        (conductorCoprimeIntegralPrime O v)) ^ n) = orderContractedIdealUnitMap O (e.prod _)
      rw [map_finsuppProd]
      apply Finsupp.prod_congr
      intro v _
      rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hcount v)]
    _ = orderContractedIdealUnitMap O I := congrArg (orderContractedIdealUnitMap O) hJI

/-- The fractional ideal class map uses the existing class of the actual invertible contraction. -/
noncomputable def orderFractionalIdealClassMap :
    RayClass.primeToModulusIdeals (orderConductorModulus O) →* ClassGroup O :=
  (ClassGroup.mk K).comp (orderFractionalContraction O)

@[simp]
theorem orderFractionalIdealClassMap_integral (I : orderPrimeToConductorIdeals O) :
    orderFractionalIdealClassMap O (orderIntegralIdealToFractional O I) =
      orderIdealClassMap O I := by
  change ClassGroup.mk K (orderFractionalContraction O (orderIntegralIdealToFractional O I)) =
    ClassGroup.mk K (orderContractedIdealUnitMap O I)
  rw [orderFractionalContraction_integral]

end NumberField
