/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm

/-!
# Open local norm images and unramified integral lifting

The norm on each actual place completion has open image. At ramification index
one its restriction to the actual integral units is surjective. The comparison
with local class field theory uses the valuative relation of the existing adic
valuation and retains the original completions and their topologies.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place WithZero ValuativeRel

namespace FunctionField.IdeleGroup

/-- The canonical valuative relation and the adic valuation have the same
actual integral subring. -/
theorem completionInteger_eq {k K : Type*} [Field k] [Field K]
    [Algebra k K] (v : Place k K) :
    let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    (ValuativeRel.valuation v.adicCompletion).integer =
      v.adicCompletionIntegers.toSubring := by
  intro hRelation
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  ext x
  change ValuativeRel.valuation v.adicCompletion x ≤ 1 ↔ Valued.v x ≤ 1
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation v.adicCompletion)
    (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)).le_one_iff_le_one

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Finite k]

/-- The actual completed local norm image is open for every finite Galois extension. -/
theorem isOpen_localNorm_range (w : Place k L) :
    IsOpen ((localNorm (K := K) w).range : Set (w.restrict K).adicCompletionˣ) := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  exact LocalClassFieldTheory.localNormSubgroup_isOpen
    (w.restrict K).adicCompletion w.adicCompletion

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

omit [FiniteDimensional K L] [IsGalois K L]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] [Finite k]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- The canonical valuation of a place completion extends the canonical
valuation of its restricted-place completion. -/
theorem completionCanonical_hasExtension [Algebra.IsIntegral K L] (w : Place k L) :
    let : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
      (ValuativeRel.valuation w.adicCompletion) := by
  intro hBaseRelation hExtensionRelation
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change algebraMap (w.restrict K).adicCompletion w.adicCompletion x ∈
    (ValuativeRel.valuation w.adicCompletion).integer ↔
    x ∈ (ValuativeRel.valuation (w.restrict K).adicCompletion).integer
  rw [completionInteger_eq, completionInteger_eq]
  change Valued.v (algebraMap (w.restrict K).adicCompletion w.adicCompletion x) ≤ 1 ↔
    Valued.v x ≤ 1
  rw [Place.algebraMap_adicCompletionComap_eq,
    Place.valued_adicCompletionComap]
  exact pow_le_one_iff_of_nonneg zero_le (w.ramificationIndex_pos (F := K)).ne'

omit [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] [Finite k]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- For the existing completed field embedding, the canonical integer ring
upstairs is the integral closure of the canonical integer ring downstairs. -/
theorem completionCanonical_isIntegralClosure (w : Place k L) :
    let : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    let _ : (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
        (ValuativeRel.valuation w.adicCompletion) :=
      completionCanonical_hasExtension (K := K) w
    IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
      w.adicCompletion := by
  intro hBaseRelation hExtensionRelation hExtension
  have : Algebra.IsAlgebraic (w.restrict K).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  have hclosure :=
    (open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsLocalRing_hensel_lift_unique
      in AlgebraicCurve.Place.isIntegralClosure_adicCompletionIntegers K w)
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  change ((algebraMap (w.restrict K).adicCompletion w.adicCompletion).comp
    (ValuativeRel.valuation (w.restrict K).adicCompletion).integer.subtype).IsIntegralElem x ↔
    ∃ y : (ValuativeRel.valuation w.adicCompletion).integer, (y : w.adicCompletion) = x
  rw [completionInteger_eq, completionInteger_eq]
  exact hclosure.isIntegral_iff

private theorem completionCanonical_span_uniformizer {k F : Type*}
    [Field k] [Field F] [Algebra k F] (v : Place k F) :
    let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    ∀ π : 𝒪[v.adicCompletion],
      Valued.v (π : v.adicCompletion) =
        (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) →
      IsLocalRing.maximalIdeal 𝒪[v.adicCompletion] = Ideal.span {π} := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  dsimp only
  intro π hπ
  ext x
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit x ↔ x ∈ Ideal.span {π}
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation v.adicCompletion (x : v.adicCompletion) < 1 ↔
    x ∈ (Ideal.span {π} : Set 𝒪[v.adicCompletion])
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  change ValuativeRel.valuation v.adicCompletion (x : v.adicCompletion) < 1 ↔
    ValuativeRel.valuation v.adicCompletion (x : v.adicCompletion) ≤
      ValuativeRel.valuation v.adicCompletion (π : v.adicCompletion)
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation v.adicCompletion)
      (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)).lt_one_iff_lt_one,
    (ValuativeRel.isEquiv (ValuativeRel.valuation v.adicCompletion)
      (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)) (x : v.adicCompletion)
      (π : v.adicCompletion), hπ]
  generalize Valued.v (x : v.adicCompletion) = a
  cases a using WithZero.recZeroCoe with
  | zero => simp only [zero_lt_one, zero_le]
  | coe z =>
    simp only [← WithZero.coe_one, WithZero.coe_lt_coe, WithZero.coe_le_coe]
    change Multiplicative.toAdd z < 0 ↔ Multiplicative.toAdd z ≤ -1
    omega

/-- Completion preserves the actual ramification index, with the canonical
integer rings used by local reciprocity. -/
theorem completionCanonical_ramificationIdx (w : Place k L) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    let _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    let _ : IsNonarchimedeanLocalField w.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField w
    let _ : (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
        (ValuativeRel.valuation w.adicCompletion) :=
      completionCanonical_hasExtension (K := K) w
    let _ : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
        w.adicCompletion := completionCanonical_isIntegralClosure (K := K) w
    let _ : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] := by
      have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
        IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
          (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
      exact Module.IsNoetherian.finite _ _
    (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion]).ramificationIdx
      𝒪[(w.restrict K).adicCompletion] = w.ramificationIndex K := by
  intro hbaseRelation hextensionRelation hbaseLocal hextensionLocal
    hextension hclosure hfinite
  have : (Valued.v : Valuation w.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation w.adicCompletion ℤᵐ⁰)
  obtain ⟨π₀, hπ₀⟩ :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
      K (w.restrict K).heightOneSpectrum
  obtain ⟨ϖ₀, hϖ₀⟩ :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
      L w.heightOneSpectrum
  let π : 𝒪[(w.restrict K).adicCompletion] :=
    ⟨π₀, by rw [completionInteger_eq]; exact π₀.2⟩
  let ϖ : 𝒪[w.adicCompletion] :=
    ⟨ϖ₀, by rw [completionInteger_eq]; exact ϖ₀.2⟩
  have hπ : Valued.v (π : (w.restrict K).adicCompletion) =
      (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hπ₀
  have hϖ : Valued.v (ϖ : w.adicCompletion) =
      (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hϖ₀
  have hvalue : Valued.v ((algebraMap 𝒪[(w.restrict K).adicCompletion]
      𝒪[w.adicCompletion] π : 𝒪[w.adicCompletion]) : w.adicCompletion) =
      Valued.v ((ϖ ^ w.ramificationIndex K : 𝒪[w.adicCompletion]) : w.adicCompletion) := by
    change Valued.v (algebraMap (w.restrict K).adicCompletion w.adicCompletion
      (π : (w.restrict K).adicCompletion)) =
      Valued.v ((ϖ : w.adicCompletion) ^ w.ramificationIndex K)
    rw [Place.algebraMap_adicCompletionComap_eq,
      Place.valued_adicCompletionComap, map_pow, hπ, hϖ]
  have hspan : Ideal.span {(algebraMap 𝒪[(w.restrict K).adicCompletion]
        𝒪[w.adicCompletion] π)} =
      (Ideal.span {ϖ ^ w.ramificationIndex K} : Ideal 𝒪[w.adicCompletion]) := by
    apply SetLike.coe_injective
    rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe,
      Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
    ext x
    change ValuativeRel.valuation w.adicCompletion (x : w.adicCompletion) ≤
      ValuativeRel.valuation w.adicCompletion
        ((algebraMap 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] π :
          𝒪[w.adicCompletion]) : w.adicCompletion) ↔
      ValuativeRel.valuation w.adicCompletion (x : w.adicCompletion) ≤
        ValuativeRel.valuation w.adicCompletion
          ((ϖ ^ w.ramificationIndex K : 𝒪[w.adicCompletion]) : w.adicCompletion)
    rw [(ValuativeRel.isEquiv (ValuativeRel.valuation w.adicCompletion)
      (Valued.v : Valuation w.adicCompletion ℤᵐ⁰)) _ _,
      (ValuativeRel.isEquiv (ValuativeRel.valuation w.adicCompletion)
      (Valued.v : Valuation w.adicCompletion ℤᵐ⁰)) _ _, hvalue]
  have hmap : (IsLocalRing.maximalIdeal 𝒪[(w.restrict K).adicCompletion]).map
      (algebraMap 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion]) =
      IsLocalRing.maximalIdeal 𝒪[w.adicCompletion] ^ w.ramificationIndex K := by
    rw [completionCanonical_span_uniformizer (w.restrict K) π hπ, Ideal.map_span,
      Set.image_singleton, hspan, completionCanonical_span_uniformizer w ϖ hϖ,
      Ideal.span_singleton_pow]
  have hKne : IsLocalRing.maximalIdeal 𝒪[(w.restrict K).adicCompletion] ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal _)
      (IsDiscreteValuationRing.not_isField _)
  have hLne : IsLocalRing.maximalIdeal 𝒪[w.adicCompletion] ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal _)
      (IsDiscreteValuationRing.not_isField _)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    (IsLocalRing.maximalIdeal 𝒪[(w.restrict K).adicCompletion])
    (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion]) hKne]
  apply Ideal.ramificationIdx'_spec
  · exact hmap.le
  · rw [hmap]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow hLne (w.ramificationIndex K))

/-- Ramification index one at the original place gives an unramified extension
of the actual completions with their canonical valuative relations. -/
theorem completionCanonical_isUnramified (w : Place k L)
    (he : w.ramificationIndex K = 1) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    let _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    let _ : IsNonarchimedeanLocalField w.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField w
    let _ : (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
        (ValuativeRel.valuation w.adicCompletion) :=
      completionCanonical_hasExtension (K := K) w
    let _ : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
        w.adicCompletion := completionCanonical_isIntegralClosure (K := K) w
    let _ : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] := by
      have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
        IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
          (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
      exact Module.IsNoetherian.finite _ _
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (w.restrict K).adicCompletion w.adicCompletion := by
  intro hbaseRelation hextensionRelation hbaseLocal hextensionLocal
    hextension hclosure hfinite
  exact ⟨(completionCanonical_ramificationIdx (K := K) w).trans he⟩

/-- If the actual place has ramification index one, every actual integral base
unit is the norm of an actual integral unit upstairs. -/
theorem exists_integral_localNorm_eq_of_ramificationIndex_eq_one (w : Place k L)
    (he : w.ramificationIndex K = 1) (x : (w.restrict K).adicCompletionˣ)
    (hx : x ∈ (w.restrict K).adicCompletionIntegers.units) :
    ∃ y : w.adicCompletionˣ, y ∈ w.adicCompletionIntegers.units ∧
      localNorm (K := K) w y = x := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  let : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  let := completionCanonical_hasExtension (K := K) w
  have : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
      w.adicCompletion := completionCanonical_isIntegralClosure (K := K) w
  have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
      (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
  have : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    Module.IsNoetherian.finite _ _
  have : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (w.restrict K).adicCompletion w.adicCompletion :=
    completionCanonical_isUnramified (K := K) w he
  have hx' : x ∈ (ValuativeRel.valuation (w.restrict K).adicCompletion).integer.units := by
    rw [completionInteger_eq]
    exact hx
  let xO : 𝒪[(w.restrict K).adicCompletion]ˣ :=
    { val := ⟨x, hx'.1⟩
      inv := ⟨(x⁻¹ : (w.restrict K).adicCompletionˣ), hx'.2⟩
      val_inv := by apply Subtype.ext; exact Units.val_inv x
      inv_val := by apply Subtype.ext; exact Units.inv_val x }
  obtain ⟨yO, hyO⟩ :=
    LocalClassFieldTheory.normIntegerUnits_surjective_unramified_of_isIntegralClosure
      (w.restrict K).adicCompletion w.adicCompletion xO
  refine ⟨LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
    w.adicCompletion yO, ?_, ?_⟩
  · rw [← completionInteger_eq w]
    exact ⟨yO.val.2, yO.inv.2⟩
  · change LocalFieldTheory.normUnits (w.restrict K).adicCompletion w.adicCompletion
      (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
        w.adicCompletion yO) = x
    rw [← LocalClassFieldTheory.normIntegerUnits_to_fieldUnits
      (w.restrict K).adicCompletion w.adicCompletion yO, hyO]
    apply Units.ext
    rfl

end FunctionField.IdeleGroup
