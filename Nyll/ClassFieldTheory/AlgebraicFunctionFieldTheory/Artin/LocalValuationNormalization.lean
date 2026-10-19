/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.GroupTheory.ArchimedeanDensely
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# The sign of the local reciprocity valuation on place completions

The local class-field construction uses the exponent of a multiplicative
valuation. The idele divisor uses its negative. The uniqueness of the ordered
integer value-group normalization identifies these two maps on the actual
place completion, without choosing a uniformizer or a new valuation.
-/

noncomputable section

open scoped WithZero

namespace FunctionField

private theorem normalizedValue_eq_valued
    (F : Type*) [Field F] [Valued F ℤᵐ⁰] [ValuativeRel F]
    [(Valued.v : Valuation F ℤᵐ⁰).Compatible] [IsNonarchimedeanLocalField F]
    (hsurj : Function.Surjective (Valued.v : Valuation F ℤᵐ⁰)) (x : F) :
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
        (ValuativeRel.valuation F x) = Valued.v x := by
  let v : Valuation F ℤᵐ⁰ := Valued.v
  let ψ : ValuativeRel.ValueGroupWithZero F →*₀ ℤᵐ⁰ :=
    MonoidWithZeroHom.ValueGroup₀.embedding.comp (ValuativeRel.ValueGroupWithZero.embed v)
  have hψ (y : F) : ψ (ValuativeRel.valuation F y) = v y := by
    change MonoidWithZeroHom.ValueGroup₀.embedding
      (ValuativeRel.ValueGroupWithZero.embed v (ValuativeRel.valuation F y)) = v y
    rw [ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict₀,
      MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    rfl
  have hmono : StrictMono ψ :=
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.comp
      (ValuativeRel.ValueGroupWithZero.embed_strictMono v)
  have honto : Function.Surjective ψ := by
    intro z
    obtain ⟨y, hy⟩ := hsurj z
    exact ⟨ValuativeRel.valuation F y, (hψ y).trans hy⟩
  let e : ValuativeRel.ValueGroupWithZero F ≃*o ℤᵐ⁰ :=
    { MulEquiv.ofBijective ψ.toMonoidHom ⟨hmono.injective, honto⟩ with
      map_le_map_iff' := hmono.le_iff_le }
  let φ := _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have : Unique (ℤᵐ⁰ ≃*o ℤᵐ⁰) := OrderMonoidIso.withZero.symm.unique
  have he : e.symm.trans φ = OrderMonoidIso.refl ℤᵐ⁰ := Subsingleton.elim _ _
  have hx := DFunLike.congr_fun he (e (ValuativeRel.valuation F x))
  change φ (e.symm (e (ValuativeRel.valuation F x))) =
    e (ValuativeRel.valuation F x) at hx
  rw [e.symm_apply_apply] at hx
  exact hx.trans (hψ x)

variable {k K : Type*} [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The valuation used by the existing local Artin map is the negative of
the order used by the all-place idele divisor. -/
theorem placeCompletion_valuationMap_eq_neg_localOrder
    (v : AlgebraicCurve.Place k K) (x : v.adicCompletionˣ) :
    let _ : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    let _ : IsNonarchimedeanLocalField v.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField v
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap v.adicCompletion
        (Additive.ofMul x) = -(IdeleGroup.localOrder v x).toAdd := by
  intro hrel hlocal
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_apply, WithZero.toAdd_unzero_eq_log,
    normalizedValue_eq_valued v.adicCompletion
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v.heightOneSpectrum)]
  change WithZero.log (Valued.v (x : v.adicCompletion)) =
    -(-WithZero.log (Valued.v (x : v.adicCompletion)))
  exact (neg_neg _).symm

end FunctionField
