/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Herbrand
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv

/-!
# The Herbrand quotient of actual integral completion units

The valuation exact sequence compares the completed field units and the trivial
integer module. Both have Herbrand quotient equal to the decomposition-group order,
so the actual integral units have quotient one, including at wildly ramified places.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped AlgebraicCurve.Place

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The actual decomposition action preserves normalized local order. -/
theorem localOrder_decomposition_smul (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.adicCompletionˣ) :
    localOrder w (σ • x) = localOrder w x := by
  let g : SemilinearAut k L := SemilinearAut.ofAlgAut (σ.val.restrictScalars k)
  have hw : g⁻¹ • w = w := (inv_smul_eq_iff).mpr σ.2.symm
  have h := congrArg (fun D : Divisor k L => D w) (divisor_smul g (placeIdele w x))
  rw [SemilinearAut.divisor_smul_apply, hw, divisor_apply, divisor_apply] at h
  change (localOrder w (component w (g • placeIdele w x))).toAdd =
    (localOrder w (component w (placeIdele w x))).toAdd at h
  rw [decomposition_smul_component, component_placeIdele_same] at h
  exact Multiplicative.ext h

end FunctionField.IdeleGroup

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped AlgebraicCurve.Place

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [IsCyclic (L ≃ₐ[K] L)]

/-- Actual integral completion units have defined Herbrand quotient one. -/
theorem decomposition_integralUnits_herbrandQuotient (w : Place k L)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    ∃ hU : HerbrandQuotientDefined (decompositionGroup (K := K) w)
        w.adicCompletionIntegers.units σ,
      let _ : Finite (HerbrandH0 (decompositionGroup (K := K) w)
        w.adicCompletionIntegers.units) := hU.1
      let _ : Finite (HerbrandHMinusOne (decompositionGroup (K := K) w)
        w.adicCompletionIntegers.units σ) := hU.2
      herbrandQuotient (G := decompositionGroup (K := K) w)
        (A := w.adicCompletionIntegers.units) σ = 1 := by
  let : MulDistribMulAction (decompositionGroup (K := K) w) (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction _
  have hB : HerbrandQuotientDefined (decompositionGroup (K := K) w)
      w.adicCompletionˣ σ := by
    have := decomposition_herbrandHMinusOne_subsingleton w σ hσ
    exact ⟨decomposition_herbrandH0_finite w, inferInstance⟩
  have hZ : HerbrandQuotientDefined (decompositionGroup (K := K) w)
      (Multiplicative ℤ) σ :=
    ⟨trivialIntHerbrandH0Finite, trivialIntHerbrandHMinusOneFinite σ⟩
  have hi : ∀ (g : decompositionGroup (K := K) w) (u : w.adicCompletionIntegers.units),
      w.adicCompletionIntegers.units.subtype (g • u) =
        g • w.adicCompletionIntegers.units.subtype u := fun _ _ => rfl
  have hj : ∀ (g : decompositionGroup (K := K) w) (a : w.adicCompletionˣ),
      localOrder w (g • a) = g • localOrder w a := localOrder_decomposition_smul w
  have hexact : ∀ a : w.adicCompletionˣ, localOrder w a = 1 ↔
      ∃ u : w.adicCompletionIntegers.units, w.adicCompletionIntegers.units.subtype u = a := by
    intro a
    constructor
    · intro ha
      exact ⟨⟨a, (localOrder_eq_zero_iff w a).mp (congrArg Multiplicative.toAdd ha)⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact Multiplicative.ext ((localOrder_eq_zero_iff w u.val).mpr u.2)
  have hsurj : Function.Surjective (localOrder w) := by
    intro n
    let hval := w.heightOneSpectrum.valuedAdicCompletion_surjective L
    exact ⟨RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
        w.adicCompletion hval n.toAdd,
      Multiplicative.ext (RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
        w.adicCompletion hval n.toAdd)⟩
  have hU := herbrandQuotientDefined_left_of_middle_right
    w.adicCompletionIntegers.units.subtype (localOrder w) hi hj hexact
    w.adicCompletionIntegers.units.subtype_injective hsurj σ hσ hB hZ
  refine ⟨hU, ?_⟩
  intro hU0 hUm
  have : Finite (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionˣ) := hB.1
  have : Finite (HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionˣ σ) := hB.2
  have : Finite (HerbrandH0 (decompositionGroup (K := K) w) (Multiplicative ℤ)) := hZ.1
  have : Finite (HerbrandHMinusOne (decompositionGroup (K := K) w) (Multiplicative ℤ) σ) := hZ.2
  have h := herbrandQuotient_multiplicative_of_shortExact
    w.adicCompletionIntegers.units.subtype (localOrder w) hi hj hexact
    w.adicCompletionIntegers.units.subtype_injective hsurj σ hσ
  rw [decomposition_fieldUnits_herbrandQuotient w σ hσ,
    trivialInt_herbrandQuotient_eq_card σ, Nat.card_eq_fintype_card] at h
  have hn : (Fintype.card (decompositionGroup (K := K) w) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (mul_right_cancel₀ hn)
  rw [one_mul]
  exact h.symm

/-- At an unramified place the actual integral-unit degree-zero Tate quotient vanishes. -/
theorem decomposition_integralUnits_herbrandH0_subsingleton_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionIntegers.units) := by
  obtain ⟨hU, h⟩ := decomposition_integralUnits_herbrandQuotient w σ hσ
  have : Subsingleton (HerbrandHMinusOne (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units σ) :=
    decompositionLocalUnits_herbrandHMinusOne_subsingleton_of_ramificationIndex_eq_one w he σ hσ
  have : Finite (HerbrandH0 (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units) := hU.1
  have : Finite (HerbrandHMinusOne (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units σ) := hU.2
  have hvalue : herbrandQuotient (G := decompositionGroup (K := K) w)
      (A := w.adicCompletionIntegers.units) σ = 1 := h
  have hcard : Nat.card
      (HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionIntegers.units) = 1 := by
    rw [herbrandQuotient_eq_card_ratio,
      Nat.card_unique (α := HerbrandHMinusOne (decompositionGroup (K := K) w)
        w.adicCompletionIntegers.units σ), Nat.cast_one, div_one] at hvalue
    exact_mod_cast hvalue
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

end FunctionField.IdeleGroup
