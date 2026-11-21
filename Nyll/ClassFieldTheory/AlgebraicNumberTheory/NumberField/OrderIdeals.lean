/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderConductor
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Extension and contraction away from an order conductor

The original inclusion of a finite integer order into the maximal order
induces inverse extension and contraction on integral ideals coprime to the
conductor. Multiplication by a conductor element turns an extended ideal
back into the actual image of the original ideal; this is the essential
arithmetic step and requires no Dedekind assumption on the smaller order.
-/

@[expose] public section

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O]

/-- Multiplication by a conductor element sends every element of an extended
ideal into the actual image of the original ideal. -/
theorem orderConductor_mul_mem_ideal_image (I : Ideal O) {x : 𝓞 K}
    (hx : x ∈ I.map (orderToRingOfIntegers O).toRingHom) :
    ∀ c ∈ orderConductor O,
      ∃ y ∈ I, orderToRingOfIntegers O y = c * x := by
  change x ∈ Submodule.span (𝓞 K)
    ((orderToRingOfIntegers O) '' (I : Set O)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c hc
      let b : O := ⟨(c : K), orderConductor_mem_order O hc⟩
      refine ⟨b * a, I.mul_mem_left b ha, ?_⟩
      rw [map_mul]
      rfl
  | zero =>
      intro c _
      exact ⟨0, I.zero_mem, by rw [map_zero, mul_zero]⟩
  | add x z _ _ hx hz =>
      intro c hc
      obtain ⟨a, ha, hax⟩ := hx c hc
      obtain ⟨b, hb, hbz⟩ := hz c hc
      refine ⟨a + b, I.add_mem ha hb, ?_⟩
      rw [map_add, hax, hbz, mul_add]
  | smul a x _ hx =>
      intro c hc
      obtain ⟨b, hb, hbx⟩ := hx (c * a) ((orderConductor O).mul_mem_right a hc)
      refine ⟨b, hb, ?_⟩
      simpa only [smul_eq_mul, mul_assoc] using hbx

/-- A coprime ideal upstairs contracts to an ideal coprime to the contracted
conductor in the original order. -/
theorem orderIdeal_comap_sup_conductor_eq_top
    (I : Ideal (𝓞 K)) (hI : I ⊔ orderConductor O = ⊤) :
    I.comap (orderToRingOfIntegers O).toRingHom ⊔
      (orderConductor O).comap (orderToRingOfIntegers O).toRingHom = ⊤ := by
  obtain ⟨a, ha, c, hc, hac⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
  let b : O := ⟨(c : K), orderConductor_mem_order O hc⟩
  have hab : orderToRingOfIntegers O (1 - b) = a := by
    rw [map_sub, map_one]
    change 1 - c = a
    exact (eq_sub_iff_add_eq.mpr hac).symm
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨1 - b, ?_, b, hc, sub_add_cancel 1 b⟩
  change orderToRingOfIntegers O (1 - b) ∈ I
  rwa [hab]

/-- A coprime ideal of the maximal order is recovered by extending its
actual contraction to the original order. -/
theorem orderIdeal_map_comap_of_coprime_conductor
    (I : Ideal (𝓞 K)) (hI : I ⊔ orderConductor O = ⊤) :
    (I.comap (orderToRingOfIntegers O).toRingHom).map
        (orderToRingOfIntegers O).toRingHom = I := by
  apply le_antisymm Ideal.map_comap_le
  obtain ⟨a, ha, c, hc, hac⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
  let b : O := ⟨(c : K), orderConductor_mem_order O hc⟩
  have hab : orderToRingOfIntegers O (1 - b) = a := by
    rw [map_sub, map_one]
    change 1 - c = a
    exact (eq_sub_iff_add_eq.mpr hac).symm
  have haMap : a ∈ (I.comap (orderToRingOfIntegers O).toRingHom).map
      (orderToRingOfIntegers O).toRingHom := by
    rw [← hab]
    apply Ideal.mem_map_of_mem
    change orderToRingOfIntegers O (1 - b) ∈ I
    rwa [hab]
  intro x hx
  let z : O := ⟨(c : K) * (x : K), hc x⟩
  have hz : z ∈ I.comap (orderToRingOfIntegers O).toRingHom := by
    change c * x ∈ I
    exact I.mul_mem_left c hx
  have hzMap := Ideal.mem_map_of_mem (orderToRingOfIntegers O).toRingHom hz
  change c * x ∈ (I.comap (orderToRingOfIntegers O).toRingHom).map
    (orderToRingOfIntegers O).toRingHom at hzMap
  have hsum := ((I.comap (orderToRingOfIntegers O).toRingHom).map
    (orderToRingOfIntegers O).toRingHom).add_mem
      (Ideal.mul_mem_right x _ haMap) hzMap
  rwa [← add_mul, hac, one_mul] at hsum

/-- Extension preserves coprimality to the conductor. -/
theorem orderIdeal_map_sup_conductor_eq_top
    (I : Ideal O)
    (hI : I ⊔ (orderConductor O).comap (orderToRingOfIntegers O).toRingHom = ⊤) :
    I.map (orderToRingOfIntegers O).toRingHom ⊔ orderConductor O = ⊤ := by
  have h := congrArg (Ideal.map (orderToRingOfIntegers O).toRingHom) hI
  rw [Ideal.map_sup, Ideal.map_top] at h
  apply top_unique
  rw [← h]
  exact sup_le_sup le_rfl Ideal.map_comap_le

/-- An ideal of the original order coprime to the conductor is recovered by
contracting its actual extension to the maximal order. -/
theorem orderIdeal_comap_map_of_coprime_conductor
    (I : Ideal O)
    (hI : I ⊔ (orderConductor O).comap (orderToRingOfIntegers O).toRingHom = ⊤) :
    (I.map (orderToRingOfIntegers O).toRingHom).comap
        (orderToRingOfIntegers O).toRingHom = I := by
  apply le_antisymm _ Ideal.le_comap_map
  obtain ⟨a, ha, c, hc, hac⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
  intro x hx
  obtain ⟨y, hy, hcy⟩ := orderConductor_mul_mem_ideal_image O I hx
    (orderToRingOfIntegers O c) hc
  have hxy : a * x + y = x := by
    apply Subalgebra.inclusion_injective (finiteSubalgebra_le_ringOfIntegers O)
    change orderToRingOfIntegers O (a * x + y) = orderToRingOfIntegers O x
    rw [map_add, map_mul, hcy]
    change orderToRingOfIntegers O a * orderToRingOfIntegers O x +
      orderToRingOfIntegers O c * orderToRingOfIntegers O x = orderToRingOfIntegers O x
    rw [← add_mul, ← map_add, hac, map_one, one_mul]
  rw [← hxy]
  exact I.add_mem (I.mul_mem_right x ha) hy

/-- Contraction is multiplicative on ideals coprime to the conductor. -/
theorem orderIdeal_comap_mul_of_coprime_conductor
    (I J : Ideal (𝓞 K))
    (hI : I ⊔ orderConductor O = ⊤) (hJ : J ⊔ orderConductor O = ⊤) :
    (I * J).comap (orderToRingOfIntegers O).toRingHom =
      I.comap (orderToRingOfIntegers O).toRingHom *
        J.comap (orderToRingOfIntegers O).toRingHom := by
  have hprod :
      (I.comap (orderToRingOfIntegers O).toRingHom *
        J.comap (orderToRingOfIntegers O).toRingHom) ⊔
          (orderConductor O).comap (orderToRingOfIntegers O).toRingHom = ⊤ :=
    (Ideal.mul_sup_eq_of_coprime_left
      (orderIdeal_comap_sup_conductor_eq_top O I hI)).trans
        (orderIdeal_comap_sup_conductor_eq_top O J hJ)
  have hmap :
      (I.comap (orderToRingOfIntegers O).toRingHom *
        J.comap (orderToRingOfIntegers O).toRingHom).map
          (orderToRingOfIntegers O).toRingHom = I * J := by
    rw [Ideal.map_mul, orderIdeal_map_comap_of_coprime_conductor O I hI,
      orderIdeal_map_comap_of_coprime_conductor O J hJ]
  rw [← hmap]
  exact orderIdeal_comap_map_of_coprime_conductor O _ hprod

/-- Extension and contraction give the actual order isomorphism on ideals
coprime to the conductor. -/
def orderCoprimeIdealEquiv :
    {I : Ideal O //
      I ⊔ (orderConductor O).comap (orderToRingOfIntegers O).toRingHom = ⊤} ≃o
    {I : Ideal (𝓞 K) // I ⊔ orderConductor O = ⊤} where
  toFun I := ⟨I.1.map (orderToRingOfIntegers O).toRingHom,
    orderIdeal_map_sup_conductor_eq_top O I.1 I.2⟩
  invFun I := ⟨I.1.comap (orderToRingOfIntegers O).toRingHom,
    orderIdeal_comap_sup_conductor_eq_top O I.1 I.2⟩
  left_inv I := Subtype.ext (orderIdeal_comap_map_of_coprime_conductor O I.1 I.2)
  right_inv I := Subtype.ext (orderIdeal_map_comap_of_coprime_conductor O I.1 I.2)
  map_rel_iff' := by
    intro I J
    constructor
    · intro h
      change I.1.map (orderToRingOfIntegers O).toRingHom ≤
        J.1.map (orderToRingOfIntegers O).toRingHom at h
      have hc := Ideal.comap_mono (f := (orderToRingOfIntegers O).toRingHom) h
      rw [orderIdeal_comap_map_of_coprime_conductor O I.1 I.2,
        orderIdeal_comap_map_of_coprime_conductor O J.1 J.2] at hc
      exact hc
    · exact Ideal.map_mono

end NumberField
