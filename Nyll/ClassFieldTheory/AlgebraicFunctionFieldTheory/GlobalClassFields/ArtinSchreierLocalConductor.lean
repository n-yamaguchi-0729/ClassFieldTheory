/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.AdjoinGenerator
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.ArtinSchreierConductor
import Nyll.AlgebraicCurves.FunctionFields.Rational.CurveRatFunc

/-!
# Local ray units are norms at an Artin–Schreier pole bound

The global generator still generates the actual completed extension. Its
pole bound therefore feeds the concrete local conductor bound, in the same
higher-unit filtration used to define the global ray class subgroup.
-/

noncomputable section
open AlgebraicCurve
open scoped WithZero AlgebraicCurve.Place ValuativeRel

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- At a pole bound divisible by p, every local ray unit is an actual norm
from the completed Artin–Schreier extension. -/
theorem artinSchreier_localHigherUnitGroup_le_norm
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (w : Place k L) (a : K) (β : L)
    (hβ : β ^ p - β = algebraMap K L a) (hgen : Algebra.adjoin K {β} = ⊤)
    (n : ℕ) (ha : (w.restrict K).adicValuation a ≤ WithZero.exp ((p * n : ℕ) : ℤ)) :
    RayClass.localHigherUnitGroup (w.restrict K) (p * n) ≤
      (IdeleGroup.localNorm (K := K) w).range := by
  let V := (w.restrict K).adicCompletion
  let W := w.adicCompletion
  let hrelation : ValuativeRel V := placeCompletionValuativeRel (w.restrict K)
  have hlocal : IsNonarchimedeanLocalField V :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have hcharV : CharP V p := (Algebra.charP_iff K V p).mp inferInstance
  let aKW : Algebra K W := ((algebraMap L W).comp (algebraMap K L)).toAlgebra
  have hKLW : IsScalarTower K L W := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hKVW : IsScalarTower K V W := IsScalarTower.of_algebraMap_eq
    (fun z => Place.adicCompletionComap_algebraMap_algebraMap K w z)
  have hβW : (algebraMap L W β) ^ p - algebraMap L W β =
      algebraMap V W (algebraMap K V a) := by
    rw [← map_pow, ← map_sub, hβ, ← IsScalarTower.algebraMap_apply K L W,
      ← IsScalarTower.algebraMap_apply K V W]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[V]
  let vV : Valuation V ℤᵐ⁰ := Valued.v
  have hvV : vV.Compatible := Valuation.Compatible.ofValuation vV
  have heqv : (ValuativeRel.valuation V).IsEquiv vV :=
    ValuativeRel.isEquiv (ValuativeRel.valuation V) vV
  have hπlt : vV (π : V) < 1 := heqv.lt_one_iff_lt_one.mp
    ((Valuation.integer.integers (ValuativeRel.valuation V)).valuation_irreducible_lt_one hπ)
  have hπbound : vV (π : V) ≤ WithZero.exp (-1 : ℤ) :=
    AlgebraicCurves.FunctionFields.Proofs.IsCurveOverRatFunc.AlgebraicCurve.le_exp_neg_one_of_lt_one
      hπlt
  have hlocalA : vV (algebraMap K V a) ≤ WithZero.exp ((p * n : ℕ) : ℤ) := by
    have hval : vV (algebraMap K V a) = (w.restrict K).adicValuation a :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (K := K) (w.restrict K).heightOneSpectrum a
    exact hval.le.trans ha
  have hscaled : (π : V) ^ (p * n) * algebraMap K V a ∈ 𝒪[V] := by
    rw [Valuation.mem_integer_iff]
    apply heqv.le_one_iff_le_one.mpr
    change vV ((π : V) ^ (p * n) * algebraMap K V a) ≤ 1
    rw [map_mul, map_pow]
    calc
      vV (π : V) ^ (p * n) * vV (algebraMap K V a) ≤
          WithZero.exp (-1 : ℤ) ^ (p * n) * WithZero.exp ((p * n : ℕ) : ℤ) :=
        mul_le_mul' (pow_le_pow_left' hπbound _) hlocalA
      _ = 1 := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
        have hcancel : (p * n) • (-1 : ℤ) + ((p * n : ℕ) : ℤ) = 0 := by
          rw [nsmul_eq_mul]
          ring
        rw [hcancel, WithZero.exp_zero]
  exact LocalClassFieldTheory.artinSchreier_fieldPrincipalUnits_le_norm V W
    p π hπ n (algebraMap K V a) hscaled (algebraMap L W β) hβW
      (IdeleGroup.completion_adjoin_generator_eq_top w β hgen)

end FunctionField
