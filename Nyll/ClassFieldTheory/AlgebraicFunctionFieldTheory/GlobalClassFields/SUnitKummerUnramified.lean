/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.AlgebraicCurves.Places.Evaluation.Value
import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegPos

/-!
# Ramification support of actual S-unit Kummer extensions

A decomposition automorphism with trivial residue action fixes every unit
Kummer root: two roots with the same residue coincide because the derivative
is a unit. The original S-unit root generators therefore make residue action
faithful away from S. The decomposition-group order formula then gives
ramification index one.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve Polynomial

private theorem decomposition_apply_eq_of_unit_kummer_root
    {k K E : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [Algebra.IsIntegral K E] (w : Place k E) (n : ℕ)
    [NeZero (n : w.ResidueField)]
    (σ τ : IdeleGroup.decompositionGroup (K := K) w)
    (hres : IdeleGroup.decompositionResidueAut (K := K) w σ =
      IdeleGroup.decompositionResidueAut (K := K) w τ)
    (a : K) (b : w.toValuationSubring) (hb : IsUnit b)
    (hpow : (b : E) ^ n = algebraMap K E a) : σ.val (b : E) = τ.val (b : E) := by
  let x := IdeleGroup.decompositionValuationEquiv w σ b
  let y := IdeleGroup.decompositionValuationEquiv w τ b
  let P : Polynomial w.toValuationSubring := X ^ n - C (b ^ n)
  have hxpow : x ^ n = b ^ n := by
    apply Subtype.ext
    change (IdeleGroup.decompositionValuationEquiv w σ b : E) ^ n = (b : E) ^ n
    rw [IdeleGroup.decompositionValuationEquiv_coe, ← map_pow, hpow, σ.val.commutes]
  have hypow : y ^ n = b ^ n := by
    apply Subtype.ext
    change (IdeleGroup.decompositionValuationEquiv w τ b : E) ^ n = (b : E) ^ n
    rw [IdeleGroup.decompositionValuationEquiv_coe, ← map_pow, hpow, τ.val.commutes]
  have hPx : P.eval x = 0 := by
    simp only [P, eval_sub, eval_pow, eval_X, eval_C, hxpow, sub_self]
  have hPy : P.eval y = 0 := by
    simp only [P, eval_sub, eval_pow, eval_X, eval_C, hypow, sub_self]
  have hxyres := congrArg (fun ρ : w.ResidueField ≃ₐ[(w.restrict K).ResidueField]
      w.ResidueField => ρ (IsLocalRing.residue w.toValuationSubring b)) hres
  rw [IdeleGroup.decompositionResidueAut_residue,
    IdeleGroup.decompositionResidueAut_residue] at hxyres
  have hdiff : ¬ IsUnit (x - y) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hxyres, sub_self]
    exact not_not_intro rfl
  have hnunit : IsUnit (n : w.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (n : w.toValuationSubring)).mp
      (by simpa only [map_natCast] using NeZero.ne (n : w.ResidueField))
  have hxunit : IsUnit x := hb.map (IdeleGroup.decompositionValuationEquiv w σ).toRingHom
  have hder : IsUnit (P.derivative.eval x) := by
    simpa only [P, derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_C, eval_pow, eval_X] using hnunit.mul (hxunit.pow (n - 1))
  have hxy := IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hPx hPy hdiff hder
  have hval := congrArg Subtype.val hxy
  simpa only [x, y, IdeleGroup.decompositionValuationEquiv_coe] using hval

namespace SUnits

variable {k K Ω : Type*} [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K] [IsSepClosure K Ω]

/-- The full S-unit Kummer extension is unramified outside S. All generators
are actual unit roots there, and the exponent is prime to the characteristic. -/
theorem kummerExtension_ramificationIndex_eq_one
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (S : Finset (Place k K)) :
    let E := kummerExtension (Ω := Ω) n S
    let _ : FiniteDimensional K E := kummerExtension_finiteDimensional n hn hmu S
    ∀ w : Place k E, w.restrict K ∉ S → w.ramificationIndex K = 1 := by
  intro E _ w hw
  have hGalois : IsGalois K E :=
    KummerTheory.kummerRadicalExtension_isGalois n (units k K S)
  have hnk : NeZero ((n : ℕ) : k) := ⟨by
    intro hzero
    apply hn
    rw [← map_natCast (algebraMap k K), hzero, map_zero]⟩
  have hnres : NeZero ((n : ℕ) : w.ResidueField) := by
    simpa only [map_natCast] using hnk.of_injective (algebraMap k w.ResidueField).injective
  have hinjective : Function.Injective (IdeleGroup.decompositionResidueAut (K := K) w) := by
    intro σ τ hστ
    apply Subtype.ext
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext K
    intro β hβ
    let b : E := ⟨β, IntermediateField.subset_adjoin K
      (KummerTheory.kummerRootSet (K := K) (Omega := Ω) n (units k K S)) hβ⟩
    have hbne : b ≠ 0 := by
      intro hzero
      exact KummerTheory.kummerRootSet_ne_zero n (units k K S) hβ
        (congrArg Subtype.val hzero)
    obtain ⟨a, ha⟩ := hβ
    have hpow : b ^ (n : ℕ) = algebraMap K E (a.val : K) := Subtype.ext ha
    have hord : w.ord b = 0 := by
      have h := congrArg w.ord hpow
      rw [← zpow_natCast, w.ord_zpow, w.ord_restrict, a.property (w.restrict K) hw,
        mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr n.ne_zero)
    obtain ⟨hbmem, hbunit⟩ := w.exists_isUnit_of_ord_eq_zero hbne hord
    exact decomposition_apply_eq_of_unit_kummer_root w (n : ℕ) σ τ hστ
      (a.val : K) ⟨b, hbmem⟩ hbunit hpow
  have hresfinite : Module.Finite (w.restrict K).ResidueField w.ResidueField :=
    Module.finite_of_finrank_pos (w.inertiaDeg_pos (F := K))
  have hcard := Nat.card_le_card_of_injective
    (IdeleGroup.decompositionResidueAut (K := K) w) hinjective
  rw [IdeleGroup.decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg] at hcard
  have hbound : Nat.card (w.ResidueField ≃ₐ[(w.restrict K).ResidueField] w.ResidueField) ≤
      w.inertiaDeg K := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have he : w.ramificationIndex K ≤ 1 :=
    (Nat.mul_le_mul_right_iff (w.inertiaDeg_pos (F := K))).mp
      (by simpa only [one_mul] using hcard.trans hbound)
  exact le_antisymm he (w.ramificationIndex_pos (F := K))

end SUnits
end FunctionField
