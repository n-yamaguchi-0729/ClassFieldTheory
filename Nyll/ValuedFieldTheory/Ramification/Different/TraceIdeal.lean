/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The actual trace image of a fractional ideal

The image uses `Algebra.trace`, including for fractional ideals with negative
valuation. Its containment in a principal fractional ideal is equivalent to
containment of the rescaled source in the existing trace-dual codifferent.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped nonZeroDivisors

namespace FractionalIdeal

variable (A : Type u) (K : Type v) {B : Type w} {L : Type x}
    [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [Module.Finite A B]

section TraceImage

variable [IsDomain A] [IsDomain B] [IsNoetherianRing B]

/-- The fractional ideal which is the image under the field trace. -/
noncomputable def traceImage (I : FractionalIdeal B⁰ L) : FractionalIdeal A⁰ K :=
  ⟨((I : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A),
    isFractional_of_fg
      (((I.fg_of_isNoetherianRing le_rfl).restrictScalars (R := A)).map
        ((Algebra.trace K L).restrictScalars A))⟩

omit [IsDomain A] in
/-- Membership is an actual trace preimage in the specified fractional ideal. -/
theorem mem_traceImage (I : FractionalIdeal B⁰ L) (a : K) :
    a ∈ traceImage A K I ↔ ∃ z ∈ I, Algebra.trace K L z = a :=
  Submodule.mem_map

omit [IsDomain A] in
/-- The trace of an element of the source lies in its trace image. -/
theorem trace_mem_traceImage {I : FractionalIdeal B⁰ L} {z : L} (hz : z ∈ I) :
    Algebra.trace K L z ∈ traceImage A K I :=
  (mem_traceImage A K I _).mpr ⟨z, hz, rfl⟩

omit [IsDomain A] in
/-- Scaling the source by a base-field element scales its actual trace image. -/
theorem traceImage_spanSingleton_mul (a : K) (I : FractionalIdeal B⁰ L) :
    traceImage A K (spanSingleton B⁰ (algebraMap K L a) * I) =
      spanSingleton A⁰ a * traceImage A K I := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (mem_traceImage A K _ y).mp hy
    obtain ⟨t, ht, rfl⟩ := mem_singleton_mul.mp hz
    refine mem_singleton_mul.mpr ⟨Algebra.trace K L t, trace_mem_traceImage A K ht, ?_⟩
    have htrace := (Algebra.trace K L).map_smul a t
    rw [Algebra.smul_def, smul_eq_mul] at htrace
    exact htrace
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_singleton_mul.mp hy
    obtain ⟨t, ht, rfl⟩ := (mem_traceImage A K I z).mp hz
    refine (mem_traceImage A K _ _).mpr
      ⟨algebraMap K L a * t, mem_singleton_mul.mpr ⟨t, ht, rfl⟩, ?_⟩
    have htrace := (Algebra.trace K L).map_smul a t
    rw [Algebra.smul_def, smul_eq_mul] at htrace
    exact htrace

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]

/-- A nonzero fractional ideal has nonzero trace image in a separable extension.
An integral basis detects a nonzero element through the nondegenerate trace pairing. -/
theorem traceImage_ne_zero {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    traceImage A K I ≠ 0 := by
  classical
  intro hzero
  apply hI
  apply eq_zero_iff.mpr
  intro z hz
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  apply b.traceDual.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply, b.traceDual_repr_apply]
  obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb i)
  have hzc : z * b i ∈ I := by
    rw [← hc, mul_comm]
    change algebraMap B L c * z ∈ (I : Submodule B L)
    simpa only [Algebra.smul_def] using (I : Submodule B L).smul_mem c hz
  have htrace := trace_mem_traceImage A K hzc
  rw [hzero, mem_zero_iff] at htrace
  exact htrace

end TraceImage

variable [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- Trace integrality of an ideal is precisely containment in the codifferent. -/
theorem traceImage_le_one_iff (I : FractionalIdeal B⁰ L) :
    traceImage A K I ≤ 1 ↔ I ≤ dual A K (1 : FractionalIdeal B⁰ L) := by
  rw [← coeToSubmodule_le_coeToSubmodule, coeToSubmodule_one]
  change (((I : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ (1 : Submodule A K)) ↔
    (I : Submodule B L) ≤ (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L)
  rw [coeToSubmodule_dual_one]
  simpa only [mul_one] using
    (Submodule.le_traceDual_iff_map_le_one
      (A := A) (K := K) (I := (I : Submodule B L)) (J := 1)).symm

/-- Trace containment at any nonzero principal fractional level is tested by
rescaling the source into the existing codifferent. -/
theorem traceImage_le_spanSingleton_iff (a : K) (ha : a ≠ 0)
    (I : FractionalIdeal B⁰ L) :
    traceImage A K I ≤ spanSingleton A⁰ a ↔
      spanSingleton B⁰ (algebraMap K L a⁻¹) * I ≤
        dual A K (1 : FractionalIdeal B⁰ L) := by
  rw [← traceImage_le_one_iff, traceImage_spanSingleton_mul, spanSingleton_mul_le_iff]
  constructor
  · intro h z hz
    obtain ⟨c, hc⟩ := (mem_spanSingleton A⁰).mp (h hz)
    apply (mem_one_iff A⁰).mpr
    refine ⟨c, ?_⟩
    rw [← hc, Algebra.smul_def, mul_comm (algebraMap A K c) a,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · intro h z hz
    obtain ⟨c, hc⟩ := (mem_one_iff A⁰).mp (h z hz)
    apply (mem_spanSingleton A⁰).mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc, mul_comm (a⁻¹ * z) a, ← mul_assoc,
      mul_inv_cancel₀ ha, one_mul]

end FractionalIdeal
