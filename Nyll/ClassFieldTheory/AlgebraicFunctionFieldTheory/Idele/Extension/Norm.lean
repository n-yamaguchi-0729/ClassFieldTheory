/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Norm.Transitivity
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.LocalRingHenselLiftUnique
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic

/-!
# The all-place idele norm

For a finite extension, each base component is the product of the field
norms over the actual finite fiber of places. The completed valuation subring is
already the integral closure of the base completed valuation subring. Thus local
norms preserve integral units, and the exceptional places of an idele norm lie in
the image of the finite exceptional set of the original idele.
-/

open scoped AlgebraicCurve.Place RestrictedProduct

noncomputable section

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The field norm on units of the actual completed extension at one place. -/
def localNorm (w : AlgebraicCurve.Place k L) :
    w.adicCompletionˣ →* (w.restrict K).adicCompletionˣ :=
  Units.map (Algebra.norm (w.restrict K).adicCompletion)

private theorem completionNorm_mem_integers (w : AlgebraicCurve.Place k L)
    (x : w.adicCompletion) (hx : x ∈ w.adicCompletionIntegers) :
    Algebra.norm (w.restrict K).adicCompletion x ∈ (w.restrict K).adicCompletionIntegers := by
  have : Algebra.IsAlgebraic (w.restrict K).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  have hclosure : IsIntegralClosure w.adicCompletionIntegers
      (w.restrict K).adicCompletionIntegers w.adicCompletion :=
    (open
      AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsLocalRing_hensel_lift_unique
      in AlgebraicCurve.Place.isIntegralClosure_adicCompletionIntegers K w)
  have hint : IsIntegral (w.restrict K).adicCompletionIntegers x :=
    hclosure.isIntegral_iff.mpr ⟨⟨x, hx⟩, rfl⟩
  have hnorm : IsIntegral (w.restrict K).adicCompletionIntegers
      (Algebra.norm (w.restrict K).adicCompletion x) :=
    Algebra.isIntegral_norm (w.restrict K).adicCompletion hint
  have : IsIntegrallyClosed (w.restrict K).adicCompletionIntegers :=
    Valuation.Integers.isIntegrallyClosed
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
        (K := K) (v := (w.restrict K).heightOneSpectrum))
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff
      (R := (w.restrict K).adicCompletionIntegers)).mp hnorm
  exact hy ▸ y.2

/-- The completed field norm sends local integral units to local integral units. -/
theorem localNorm_mem_localUnits (w : AlgebraicCurve.Place k L)
    (x : w.adicCompletionˣ) (hx : x ∈ w.adicCompletionIntegers.units) :
    localNorm (K := K) w x ∈ (w.restrict K).adicCompletionIntegers.units := by
  obtain ⟨hx, hxinv⟩ := (Submonoid.mem_units_iff _ x).mp hx
  apply (Submonoid.mem_units_iff _ _).mpr
  constructor
  · exact completionNorm_mem_integers w (x : w.adicCompletion) hx
  · rw [← map_inv (localNorm (K := K) w) x]
    exact completionNorm_mem_integers w ((x⁻¹ : w.adicCompletionˣ) : w.adicCompletion) hxinv

/-- A local completed norm with its codomain identified with the specified base place. -/
def localNormOver (v : AlgebraicCurve.Place k K) (w : AlgebraicCurve.Place k L)
    (hw : w.restrict K = v) : w.adicCompletionˣ →* v.adicCompletionˣ :=
  hw ▸ localNorm (K := K) w

/-- Equality of the restricted place transports the actual integer-unit condition. -/
theorem localNormOver_mem_localUnits (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v)
    (x : w.adicCompletionˣ) (hx : x ∈ w.adicCompletionIntegers.units) :
    localNormOver v w hw x ∈ v.adicCompletionIntegers.units := by
  subst v
  exact localNorm_mem_localUnits w x hx

/-- The component of the idele norm is the product over the actual finite fiber. -/
def normComponent (v : AlgebraicCurve.Place k K) :
    IdeleGroup k L →* v.adicCompletionˣ where
  toFun a := ∏ w : v.fiberOver L,
    localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) (a w.1)
  map_one' := by
    simp only [RestrictedProduct.one_apply, map_one, Finset.prod_const_one]
  map_mul' a b := by
    simp only [RestrictedProduct.mul_apply, map_mul, Finset.prod_mul_distrib]

@[simp]
theorem normComponent_apply (v : AlgebraicCurve.Place k K) (a : IdeleGroup k L) :
    normComponent (k := k) (K := K) (L := L) v a = ∏ w : v.fiberOver L,
      localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) (a w.1) :=
  rfl

/-- A finite product of local norms is integral when every source component is integral. -/
theorem normComponent_mem_localUnits (v : AlgebraicCurve.Place k K)
    (a : IdeleGroup k L) (ha : ∀ w ∈ v.fiberOver L, a w ∈ w.adicCompletionIntegers.units) :
    normComponent (k := k) (K := K) (L := L) v a ∈ v.adicCompletionIntegers.units := by
  rw [normComponent_apply]
  apply Subgroup.prod_mem
  intro w _
  exact localNormOver_mem_localUnits v w.1
    ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) (a w.1) (ha w.1 w.2)

private theorem normComponent_eventually_mem_localUnits (a : IdeleGroup k L) :
    ∀ᶠ v : AlgebraicCurve.Place k K in Filter.cofinite,
      normComponent (k := k) (K := K) (L := L) v a ∈ v.adicCompletionIntegers.units := by
  have hbad : {w : AlgebraicCurve.Place k L | a w ∉ w.adicCompletionIntegers.units}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have haway : ∀ᶠ v : AlgebraicCurve.Place k K in Filter.cofinite,
      v ∉ (fun w : AlgebraicCurve.Place k L => w.restrict K) ''
        {w : AlgebraicCurve.Place k L | a w ∉ w.adicCompletionIntegers.units} :=
    (hbad.image (fun w : AlgebraicCurve.Place k L => w.restrict K)).compl_mem_cofinite
  apply haway.mono
  intro v hv
  apply normComponent_mem_localUnits v a
  intro w hw
  by_contra hbadw
  exact hv ⟨w, hbadw, (AlgebraicCurve.Place.mem_fiberOver v).mp hw⟩

/-- The norm on all-place ideles, with its restricted-product condition proved from
local integrality and the image of the finite exceptional set. -/
def norm : IdeleGroup k L →* IdeleGroup k K where
  toFun a := ⟨fun v => normComponent (k := k) (K := K) (L := L) v a,
    normComponent_eventually_mem_localUnits (K := K) a⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (normComponent (k := k) (K := K) (L := L) v)
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (normComponent (k := k) (K := K) (L := L) v) a b

@[simp]
theorem component_norm (v : AlgebraicCurve.Place k K) (a : IdeleGroup k L) :
    component v (norm (K := K) (L := L) a) = ∏ w : v.fiberOver L,
      localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) (a w.1) :=
  rfl

end FunctionField.IdeleGroup
