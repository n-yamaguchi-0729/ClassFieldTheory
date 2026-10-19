/-
Copyright 2026 Anthropic, PBC.
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors of local additions: Naganori Yamaguchi (assisted by OpenAI Codex).

Adapted Anthropic FLT sources at pinned comparison revision:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean
The exact upstream source-file correspondence remains unresolved for:
RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
RationalFunctionField_ord_placeInfty
RationalFunctionField_ord_placeInfty_algebraMap
RationalFunctionField_eq_placeInfty_of_ord_X_neg
RationalFunctionField_deg_placeInfty
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.Valuation
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.ValuationRings.OrdEqNegLogValuationSubringEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncToValuationSubringEq
import Mathlib.Util.WithWeakNamespace
import Lean.Elab.Tactic.Omega
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Basic

/-!
# InfinityArithmetic

Orders, polynomial integrality, and residue degree at the place at infinity.
-/

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

with_weak_namespace _root_.AlgebraicCurve.RationalFunctionField
theorem ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] (v : Place K
  (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
  v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K} (hf : f ≠ 0) : v.ord f = -f.intDegree := by
  classical
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K)
      (AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
        v hv).symm hπ hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]
end RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_placeInfty {K : Type*} [Field K]
  [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree :=
  AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
    (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K) hf
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty
end ProofImplementation

end

section

namespace AlgebraicCurve.RationalFunctionField

theorem ord_placeInfty_X (K : Type*) [Field K]
  [DecidableEq (RatFunc K)] : (RationalFunctionField.placeInfty K).ord (RatFunc.X : RatFunc K) =
  -1 := by
  rw [ord_placeInfty (K := K) RatFunc.X_ne_zero, RatFunc.intDegree_X]

end AlgebraicCurve.RationalFunctionField

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty_algebraMap

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap {K : Type*} [Field K]
  [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap
  (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty (RatFunc.algebraMap_ne_zero hq),
    RatFunc.intDegree_polynomial]
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty_algebraMap
end ProofImplementation

end

section

namespace AlgebraicCurve.RationalFunctionField

theorem algebraMap_polynomial_mem_of_ne_placeInfty (K :
  Type*) [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) (q : (Polynomial K)) :
    algebraMap (Polynomial K) (RatFunc K) q ∈ u.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, hw⟩ | hw
  · subst hw; exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd hw hu

end AlgebraicCurve.RationalFunctionField

end

section

namespace AlgebraicCurve.RationalFunctionField

theorem ord_X_nonneg_of_ne_placeInfty (K : Type*)
  [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact u.ord_nonneg_of_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hu Polynomial.X)

end AlgebraicCurve.RationalFunctionField

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_eq_placeInfty_of_ord_X_neg

open AlgebraicCurve

namespace S09CD

theorem eq_placeInfty_of_ord_X_neg {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K
  (RatFunc K))
    (hv : v.ord (RatFunc.X : RatFunc K) < 0) : v = RationalFunctionField.placeInfty K := by
  rcases RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | h
  · exfalso
    have hmem := RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum (K := K) w Polynomial.X
    rw [RatFunc.algebraMap_X] at hmem
    have := (Place.mem_iff_ord_nonneg _ RatFunc.X_ne_zero).mp hmem
    omega
  · exact h

end S09CD

theorem _root_.AlgebraicCurve.RationalFunctionField.eq_placeInfty_of_ord_X_neg {K : Type*} [Field
  K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : v.ord (RatFunc.X : RatFunc K) < 0) :
  v = RationalFunctionField.placeInfty K :=
  S09CD.eq_placeInfty_of_ord_X_neg v hv
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_eq_placeInfty_of_ord_X_neg
end ProofImplementation

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum

open _root_.AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve

namespace WFg
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by rw [map_zero, sub_self])⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa only [map_zero, sub_zero] using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt_left hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

end WFg

end AlgebraicCurve.RationalFunctionField

end

theorem _root_.AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
  {K : Type*} [Field K] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum
  (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.deg = 1 := by
  classical
  have hvS : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring :=
    AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum v hv
  have hequiv : (RatFunc.inftyValuation K).IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hvS.symm
  have hbij : Function.Bijective (Algebra.ofId K v.ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K v.ResidueField).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      have hx' : RatFunc.inftyValuation K x ≤ 1 := by
        rw [hvS] at hx
        exact (Valuation.mem_valuationSubring_iff _ _).mp hx
      obtain ⟨c, hc⟩ :=
        AlgebraicCurve.RationalFunctionField.WFg.exists_sub_algebraMap_intDegree_neg K hx'
      refine ⟨c, ?_⟩
      change IsLocalRing.residue _ (algebraMap K v.toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      change v.adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← hequiv.lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]
end RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_deg_placeInfty

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem _root_.AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K]
  [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 :=
  AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K)
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_deg_placeInfty
end ProofImplementation

end
