/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The local invariant at a finite unramified layer

The class of a base unit is the actual degree-two carry class for arithmetic
Frobenius. Its invariant is the usual valuation divided by the degree,
viewed in `ℚ/ℤ`. The valuation-ring uniformizer has invariant `1 / [L : K]`.
-/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ClassFieldTower.Cohomology LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ClassFieldTheory.Brauer

/-- The canonical inclusion of the group of residues modulo a positive
denominator into `ℚ/ℤ`. -/
def zmodToRationalCircle (d : ℕ) (hd : 0 < d) : ZMod d →+ AddCircle (1 : ℚ) := by
  let q : AddCircle (1 : ℚ) := ((1 : ℚ) / d : ℚ)
  have hq : (d : ℤ) • q = 0 := by
    rw [natCast_zsmul]
    change d • (((1 : ℚ) / d : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd.ne'),
      AddCircle.coe_period]
  exact ZMod.lift d ⟨zmultiplesHom (AddCircle (1 : ℚ)) q, hq⟩

/-- Reducing an integer numerator does not change the rational class. -/
@[simp]
theorem zmodToRationalCircle_intCast (d : ℕ) (hd : 0 < d) (m : ℤ) :
    zmodToRationalCircle d hd (m : ZMod d) = ((m : ℚ) / d : ℚ) := by
  rw [zmodToRationalCircle, ZMod.lift_coe]
  change m • (((1 : ℚ) / d : ℚ) : AddCircle (1 : ℚ)) = ((m : ℚ) / d : ℚ)
  rw [← AddCircle.coe_zsmul]
  apply congrArg (fun x : ℚ => (x : AddCircle (1 : ℚ)))
  rw [zsmul_eq_mul, ← mul_div_assoc, mul_one]

/-- The inclusion with a fixed positive denominator is injective. -/
theorem zmodToRationalCircle_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (zmodToRationalCircle d hd) := by
  let : Fact (0 < (1 : ℚ)) := ⟨zero_lt_one⟩
  rw [zmodToRationalCircle, ZMod.lift_injective]
  intro m hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  change m • (((1 : ℚ) / d : ℚ) : AddCircle (1 : ℚ)) = 0 at hm
  rw [← AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hd]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hm

/-- A rational-circle class lies in the fixed-denominator image exactly
when its order divides that denominator. -/
theorem mem_range_zmodToRationalCircle_iff (d : ℕ) (hd : 0 < d) (x : AddCircle (1 : ℚ)) :
    x ∈ (zmodToRationalCircle d hd).range ↔ d • x = 0 := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod d), ZMod.natCast_self, zero_smul, map_zero]
  · intro hx
    let : Fact (0 < (1 : ℚ)) := ⟨zero_lt_one⟩
    obtain ⟨m, _, hm⟩ := (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) hd).mp hx
    rw [mul_one] at hm
    have h := zmodToRationalCircle_intCast d hd (m : ℤ)
    simp only [Int.cast_natCast] at h
    exact ⟨(m : ZMod d), h.trans hm⟩

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]

/-- Arithmetic Frobenius gives the canonical carry class of a base unit
in the actual degree-two cohomology of the unramified Galois extension. -/
def unramifiedClass : Additive Kˣ →+ groupCohomology (liftedGaloisUnitsRep K L) 2 := by
  let : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
  exact cyclicUnitClass K L (arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_generates K L)

omit [IsUniformAddGroup L] [LocalFieldTheory.ValuativeExtension K L] in
/-- Evaluation of the arithmetic carry class at a specified base unit. -/
theorem unramifiedClass_apply (a : Kˣ) :
    let _ : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
    unramifiedClass K L (Additive.ofMul a) =
      liftedCyclicBaseUnitH2Class K L (arithmeticFrobeniusOfUnramifiedValuation K L)
        (arithmeticFrobeniusOfUnramifiedValuation_generates K L) a := by
  intro cyclic
  rfl

omit [IsUniformAddGroup L] [LocalFieldTheory.ValuativeExtension K L] in
/-- The arithmetic carry class vanishes exactly when the base unit is a
norm from the actual upper field. -/
theorem unramifiedClass_eq_zero_iff_norm (a : Kˣ) :
    unramifiedClass K L (Additive.ofMul a) = 0 ↔ a ∈ localNormSubgroup K L := by
  let : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
  exact cyclicUnitClass_eq_zero_iff_norm K L (arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_generates K L) a

omit [IsUniformAddGroup L] [LocalFieldTheory.ValuativeExtension K L] in
/-- Each degree-two class at the unramified layer has an actual base-unit
carry representative. -/
theorem unramifiedClass_surjective : Function.Surjective (unramifiedClass K L) := by
  let : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
  exact cyclicUnitClass_surjective K L (arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_generates K L)

/-- The kernel of the unramified carry class is the kernel of valuation modulo the degree. -/
theorem unramifiedClass_ker :
    (unramifiedClass K L).ker = (valuationModDegree K (Module.finrank K L)).ker := by
  ext a
  change unramifiedClass K L (Additive.ofMul a.toMul) = 0 ↔
    valuationModDegree K (Module.finrank K L) a = 0
  rw [unramifiedClass_eq_zero_iff_norm,
    mem_normSubgroup_unramifiedValuation_iff_finrank_dvd_valuation_of_isIntegralClosure K L,
    valuationModDegree_eq_zero_iff_dvd]
  rfl

/-- The arithmetic invariant identifies the relative group with the
residues of the usual valuation modulo the extension degree. -/
def unramifiedInvariantEquiv :
    groupCohomology (liftedGaloisUnitsRep K L) 2 ≃+ ZMod (Module.finrank K L) :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective (unramifiedClass K L)
      (unramifiedClass_surjective K L)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (unramifiedClass_ker K L)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective (valuationModDegree K (Module.finrank K L))
        (valuationModDegree_surjective K (Module.finrank K L))))).trans (AddEquiv.neg _)

/-- The usual positive valuation is the negative of the valuation used in
the multiplicative value-group exact sequence. -/
@[simp]
theorem unramifiedInvariantEquiv_class (a : Kˣ) :
    unramifiedInvariantEquiv K L (unramifiedClass K L (Additive.ofMul a)) =
      ((-valuationMap K (Additive.ofMul a) : ℤ) : ZMod (Module.finrank K L)) := by
  let C := QuotientAddGroup.quotientKerEquivOfSurjective (unramifiedClass K L)
    (unramifiedClass_surjective K L)
  have hC : C.symm (unramifiedClass K L (Additive.ofMul a)) =
      QuotientAddGroup.mk (Additive.ofMul a) := by
    apply C.injective
    exact C.apply_symm_apply (unramifiedClass K L (Additive.ofMul a))
  change -(QuotientAddGroup.quotientKerEquivOfSurjective (valuationModDegree K (Module.finrank K L))
    (valuationModDegree_surjective K (Module.finrank K L))
      (QuotientAddGroup.quotientAddEquivOfEq (unramifiedClass_ker K L)
        (C.symm (unramifiedClass K L (Additive.ofMul a))))) = _
  rw [hC, QuotientAddGroup.quotientAddEquivOfEq_mk]
  change -valuationModDegree K (Module.finrank K L) (Additive.ofMul a) = _
  rw [valuationModDegree_apply, Int.cast_neg]

/-- The invariant of the actual degree-two group of the finite unramified
layer, with values in `ℚ/ℤ`. -/
def unramifiedInvariant : groupCohomology (liftedGaloisUnitsRep K L) 2 →+ AddCircle (1 : ℚ) :=
  (zmodToRationalCircle (Module.finrank K L) Module.finrank_pos).comp
    (unramifiedInvariantEquiv K L).toAddMonoidHom

/-- Evaluation on the arithmetic carry class of a unit. -/
@[simp]
theorem unramifiedInvariant_class (a : Kˣ) :
    unramifiedInvariant K L (unramifiedClass K L (Additive.ofMul a)) =
      (((-valuationMap K (Additive.ofMul a) : ℤ) : ℚ) / Module.finrank K L : ℚ) := by
  change zmodToRationalCircle (Module.finrank K L) Module.finrank_pos
    (unramifiedInvariantEquiv K L (unramifiedClass K L (Additive.ofMul a))) = _
  rw [unramifiedInvariantEquiv_class, zmodToRationalCircle_intCast]

/-- The invariant at each finite unramified layer is injective. -/
theorem unramifiedInvariant_injective : Function.Injective (unramifiedInvariant K L) :=
  (zmodToRationalCircle_injective (Module.finrank K L) Module.finrank_pos).comp
    (unramifiedInvariantEquiv K L).injective

/-- The values of the finite-layer invariant are exactly the degree-torsion
subgroup in `ℚ/ℤ`. -/
theorem mem_range_unramifiedInvariant_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (unramifiedInvariant K L).range ↔ Module.finrank K L • x = 0 := by
  rw [← mem_range_zmodToRationalCircle_iff (Module.finrank K L) Module.finrank_pos]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨unramifiedInvariantEquiv K L y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(unramifiedInvariantEquiv K L).symm y, ?_⟩
    change zmodToRationalCircle (Module.finrank K L) Module.finrank_pos
      ((unramifiedInvariantEquiv K L) ((unramifiedInvariantEquiv K L).symm y)) = _
    rw [AddEquiv.apply_symm_apply]

/-- The class of an actual valuation-ring uniformizer has positive
arithmetic invariant `1 / [L : K]`. -/
theorem unramifiedInvariant_uniformizer :
    unramifiedInvariant K L
      (unramifiedClass K L (Additive.ofMul (integerRingUniformizerFieldUnit K))) =
        ((1 : ℚ) / Module.finrank K L : ℚ) := by
  rw [unramifiedInvariant_class, valuationMap_apply, v_integerRingUniformizerFieldUnit,
    neg_neg, Int.cast_one]

end ClassFieldTheory.Brauer
