/-
Copyright 2026 Anthropic, PBC.
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors of local additions: Naganori Yamaguchi (assisted by OpenAI Codex).

Adapted Anthropic FLT sources at pinned comparison revision:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean
The exact upstream source-file correspondence remains unresolved for:
RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
RationalFunctionField_ord_ofHeightOneSpectrum_of_span
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.ValuationRings.OrdEqNegLogValuationSubringEq
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# FiniteOrder

Orders at polynomial primes and rational points, expressed by valuations and root multiplicity.
-/

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log {K :
  Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K}
  (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) :
  (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f = -WithZero.log (w.valuation
  (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    exact w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf
end RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

end

section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_ord_ofHeightOneSpectrum_of_span

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span {K : Type*}
  [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp :
  p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F :=
  RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    exact w.valuation_of_algebraMap (K := RatFunc K) p
  rw [AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log w hp hw
    (RatFunc.algebraMap_ne_zero hp), hval]
  rw [log_exp, neg_neg]
end RationalFunctionField_ord_ofHeightOneSpectrum_of_span
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

end

section

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFieldOrdPlaceOfPoint

variable {K : Type*} [Field K]

private theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa only [mul_zero] using hr)
  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)
  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    exact hndvd (((ord_finitePlace_ne_zero_iff K (irreducible_X_sub_C a) hr0).mp) hcon)
  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap {K : Type*} [Field
  K] (a : K) {q : Polynomial K} (hq : q ≠ 0) : (placeOfPoint K a).ord (algebraMap (Polynomial K)
  (RatFunc K) q) = Polynomial.rootMultiplicity a q := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq]
  have hlinear : (placeOfPoint K a).ord
      (algebraMap K[X] (RatFunc K) (X - C a)) = 1 :=
    ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a))
      (X_sub_C_ne_zero a) (heightOneSpectrumOfIrreducible_asIdeal K (irreducible_X_sub_C a))
  rw [hlinear, mul_one]

end AlgebraicCurves.Places.Rational.Proofs.RationalFieldOrdPlaceOfPoint

end
