/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.PrimePowerDescent
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower

/-!
# Completion preserves purely inseparable function-field degrees

A prime-degree purely inseparable extension cannot shrink on completion:
a root of its defining prime-power polynomial in the base completion would
descend to the original function field. A tower of prime-degree extensions
then gives the result for every finite purely inseparable extension.
-/

noncomputable section
open AlgebraicCurve Polynomial
open AlgebraicCurves.Places.Proofs
open Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2
open scoped AlgebraicCurve.Place WithZero

namespace FunctionField

/-- Completion cannot increase the degree of a finite extension. -/
theorem finrank_adicCompletion_le
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] (w : Place k L) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion ≤ Module.finrank K L := by
  let hRankOne : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    Place.kw_ffgc_rankOne_adicCompletion (w.restrict K)
  let hNormed : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  let b := Module.finBasis K L
  have hsurj : Function.Surjective (Place.kw_ffgc_completionLinearCombination K w b) := by
    rw [← Set.range_eq_univ, ← LinearMap.coe_range,
      ← (LinearMap.range
        (Place.kw_ffgc_completionLinearCombination K w b)).closed_of_finiteDimensional.closure_eq]
    exact (Place.denseRange_completionLinearCombination K w b).closure_range
  have h := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa only [Module.finrank_fin_fun] using h

private theorem finrank_adicCompletion_eq_prime_of_root
    {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] (w : Place k L)
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) (β : L)
    (hβ : β ^ p = algebraMap K L a) (ha : ∀ b : K, b ^ p ≠ a)
    (hdegree : Module.finrank K L = p) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion = p := by
  have hnot : ∀ b : (w.restrict K).adicCompletion,
      b ^ p ≠ algebraMap K (w.restrict K).adicCompletion a := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_pow_eq_of_completion_pow_eq (w.restrict K) p a b hb
    exact ha c hc
  have hirr : Irreducible (X ^ p - C (algebraMap K (w.restrict K).adicCompletion a)) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hnot
  have hroot : aeval (algebraMap L w.adicCompletion β)
      (X ^ p - C (algebraMap K (w.restrict K).adicCompletion a)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← map_pow, hβ,
      Place.adicCompletionComap_algebraMap_algebraMap K w, sub_self]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot
    (monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)
  have hlower := minpoly.natDegree_le
    (A := (w.restrict K).adicCompletion) (algebraMap L w.adicCompletion β)
  rw [← hmin, natDegree_X_pow_sub_C] at hlower
  exact (finrank_adicCompletion_le w |>.trans_eq hdegree).antisymm hlower

private theorem exists_prime_adjoin_of_isPurelyInseparable
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hdegree : 1 < Module.finrank K L) :
    ∃ (a : K) (β : L), β ^ p = algebraMap K L a ∧
      (∀ b : K, b ^ p ≠ a) ∧
      Module.finrank K (IntermediateField.adjoin K {β}) = p := by
  have hns : ¬ Function.Surjective (algebraMap K L) := by
    intro hsurj
    have hone := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap K L).injective, hsurj⟩
    omega
  obtain ⟨x, hx⟩ := not_forall.mp hns
  have hexp : 0 < IsPurelyInseparable.elemExponent K x := by
    by_contra h
    have heq : IsPurelyInseparable.elemExponent K x = 0 := by omega
    have hmem := IsPurelyInseparable.elemExponent_def' K p x
    rw [heq, pow_zero, pow_one] at hmem
    exact hx hmem
  let β : L := x ^ p ^ (IsPurelyInseparable.elemExponent K x - 1)
  let a : K := IsPurelyInseparable.elemReduct K x
  have hβ : β ^ p = algebraMap K L a := by
    dsimp only [β, a]
    rw [← pow_mul, ← pow_succ,
      Nat.sub_add_cancel hexp, IsPurelyInseparable.algebraMap_elemReduct_eq' K p x]
  have hβnot : β ∉ (algebraMap K L).range :=
    IsPurelyInseparable.elemExponent_min' K p (by omega)
  have hLp : CharP L p := (Algebra.charP_iff K L p).mp inferInstance
  have ha : ∀ b : K, b ^ p ≠ a := by
    intro b hb
    apply hβnot
    refine ⟨b, ?_⟩
    apply frobenius_inj L p
    change (algebraMap K L b) ^ p = β ^ p
    rw [← map_pow, hb, hβ]
  have hirr : Irreducible (X ^ p - C a) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) ha
  have heval : aeval β (X ^ p - C a) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr heval
    (monic_X_pow_sub_C a (Fact.out : p.Prime).ne_zero)
  refine ⟨a, β, hβ, ha, ?_⟩
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β),
    ← hmin, natDegree_X_pow_sub_C]

private theorem finrank_adicCompletion_eq_of_isPurelyInseparable_aux
    (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (K : Type) [Field K] [Algebra k K] [Algebra K L] [IsScalarTower k K L]
      [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
      [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L],
      Module.finrank K L = n → ∀ w : Place k L,
      Module.finrank (w.restrict K).adicCompletion w.adicCompletion = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro K hK akK aKL hkKL aRK hkRK hfunction hchar hfinite hpure hdegree w
    by_cases hone : Module.finrank K L = 1
    · have hle := finrank_adicCompletion_le (K := K) w
      have hpos := Module.finrank_pos (R := (w.restrict K).adicCompletion)
        (M := w.adicCompletion)
      omega
    have hn : 1 < Module.finrank K L :=
      lt_of_le_of_ne (Module.finrank_pos : 0 < Module.finrank K L) (Ne.symm hone)
    obtain ⟨a, β, hβ, ha, hMdegree⟩ :=
      exists_prime_adjoin_of_isPurelyInseparable K L p hn
    let M : IntermediateField K L := IntermediateField.adjoin K {β}
    let βM : M := ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
    have hβM : βM ^ p = algebraMap K M a := by
      apply Subtype.ext
      exact hβ
    have hkML : IsScalarTower k M L := IsScalarTower.to₁₃₄ k K M L
    have hML : FiniteDimensional M L := FiniteDimensional.right K M L
    have hMsep : IsPurelyInseparable M L := IsPurelyInseparable.tower_top K M L
    have hMp : CharP M p := (Algebra.charP_iff K M p).mp inferInstance
    let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K M
    let aRM : Algebra (RatFunc k) M := presentation.val
    have hkRM : IsScalarTower k (RatFunc k) M := presentation.property.1
    have hMfunction : FunctionField k M := presentation.property.2
    have hprod : p * Module.finrank M L = n := by
      rw [← hMdegree]
      exact (Module.finrank_mul_finrank K M L).trans hdegree
    have hless : Module.finrank M L < n := by
      have hp : 1 < p := (Fact.out : p.Prime).one_lt
      have hpos : 0 < Module.finrank M L := Module.finrank_pos
      nlinarith
    have hupper := ih (Module.finrank M L) hless M rfl w
    have hlower := finrank_adicCompletion_eq_prime_of_root
      (w.restrict M) p a βM hβM ha hMdegree
    have hfiniteLower : FiniteDimensional ((w.restrict M).restrict K).adicCompletion
        (w.restrict M).adicCompletion := inferInstance
    have hw : (w.restrict M).restrict K = w.restrict K :=
      restrict_restrict (F := K) (E := M) w
    let aVM : Algebra (w.restrict K).adicCompletion (w.restrict M).adicCompletion :=
      (IdeleGroup.completionMapOver (w.restrict K) (w.restrict M) hw).toAlgebra
    have hVM : FiniteDimensional (w.restrict K).adicCompletion
        (w.restrict M).adicCompletion := by
      cases hw
      exact hfiniteLower
    have hlower' : Module.finrank (w.restrict K).adicCompletion
        (w.restrict M).adicCompletion = p := by
      cases hw
      exact hlower
    have htower : IsScalarTower (w.restrict K).adicCompletion
        (w.restrict M).adicCompletion w.adicCompletion :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (congrArg (fun f : (w.restrict K).adicCompletion →+* w.adicCompletion => f x)
          (IdeleGroup.completionMapOver_trans (w.restrict K) (w.restrict M) w
            hw rfl rfl)).symm
    calc
      Module.finrank (w.restrict K).adicCompletion w.adicCompletion =
          Module.finrank (w.restrict K).adicCompletion (w.restrict M).adicCompletion *
            Module.finrank (w.restrict M).adicCompletion w.adicCompletion :=
        (Module.finrank_mul_finrank (w.restrict K).adicCompletion
          (w.restrict M).adicCompletion w.adicCompletion).symm
      _ = n := by rw [hlower', hupper]; exact hprod

/-- A finite purely inseparable extension of a function field has the same
degree after completing at any of its places. -/
theorem finrank_adicCompletion_eq_of_isPurelyInseparable
    {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsPurelyInseparable K L] (w : Place k L) :
    Module.finrank (w.restrict K).adicCompletion w.adicCompletion = Module.finrank K L := by
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  have hKp : CharP K (ringChar k) := (Algebra.charP_iff k K (ringChar k)).mp inferInstance
  exact finrank_adicCompletion_eq_of_isPurelyInseparable_aux k L (ringChar k)
    (Module.finrank K L) K rfl w

end FunctionField
