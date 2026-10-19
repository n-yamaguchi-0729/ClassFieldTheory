/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Residues.RationalSimplePoles
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Residues.Construction
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Places.Rational.RatFuncGlobalResidueFormula
import Nyll.AlgebraicCurves.Places.Rational.RatFuncTraceLocalResidueFinitePlaceDivPowEqZero
import Nyll.AlgebraicCurves.Places.Rational.RatFuncTraceLocalResiduePlaceInftyXPowEqZero
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The residue theorem over a perfect rational-function field

Partial fractions reduce the residue sum to polynomial monomials and principal parts.
The local residue computations and differential orders come from the shared rational core.
-/

namespace AlgebraicCurves.Differentials.Residues.Proofs.RatFuncResidue
namespace AlgebraicCurve
end AlgebraicCurve

open _root_.IsDedekindDomain _root_.WithZero _root_.Module _root_.IsLocalRing
open _root_.Module.IsLocalRing _root_.KaehlerDifferential _root_.Polynomial
open _root_.AlgebraicCurve _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurves.Differentials.Residues.Proofs
open RationalSimplePoles.AlgebraicCurve RationalSimplePoles.AlgebraicCurve.RationalFunctionField
open RatFuncResidue.AlgebraicCurve
open _root_.UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial
  Ω[F⁄K]] in
theorem exists_smul_eq_of_ne_zero (v : Place K F) {ω ω₀ : Ω[F⁄K]}
    (hω : ω ≠ 0) (hω₀ : ω₀ ≠ 0) : ∃ g : F, g ≠ 0 ∧ ω = g • ω₀ := by
  set a := v.differentialCoeff ω with ha
  set b := v.differentialCoeff ω₀ with hb
  have h0 : b ≠ 0 := v.differentialCoeff_ne_zero hω₀
  refine ⟨a * b⁻¹, mul_ne_zero (v.differentialCoeff_ne_zero hω) (inv_ne_zero h0), ?_⟩
  have hω₀eq : ω₀ = b • v.dCoord := hb ▸ (v.differentialCoeff_smul_dCoord ω₀).symm
  rw [hω₀eq, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  exact ha ▸ (v.differentialCoeff_smul_dCoord ω).symm

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

variable (K F) in
/-- The diagonal embedding into the adele space as a linear map over the constant field. -/
def principalAdele : F →ₗ[K] adeleSpace K F where
  toFun f := ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
  map_add' f g := Subtype.ext ((diagonalHom K F).map_add f g)
  map_smul' c f := Subtype.ext ((diagonalHom K F).map_smul c f)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The nonnegative powers of the rational coordinate. -/
def P1PolynomialGenerators : Set (RatFunc K) := Set.range fun n : ℕ => RatFunc.X ^ n

/-- Principal parts with monic irreducible denominators and smaller-degree numerators. -/
def P1PrincipalPartGenerators : Set (RatFunc K) :=
  {f | ∃ (p c : K[X]) (m : ℕ), p.Monic ∧ Irreducible p ∧ c.degree < p.degree ∧ 1 ≤ m ∧
    f = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m}

/-- Polynomial monomials and the principal parts used in partial-fraction decomposition. -/
def P1PartialFractionGenerators : Set (RatFunc K) :=
  P1PolynomialGenerators K ∪ P1PrincipalPartGenerators K

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
theorem algebraMap_polynomial_mem_span_P1PolynomialGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PolynomialGenerators K) := by
  rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    ← RatFunc.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
theorem pow_X_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n ∈ v.toValuationSubring := by
  have h : algebraMap K[X] (RatFunc K) (Polynomial.X ^ n) ∈ v.toValuationSubring :=
    algebraMap_polynomial_mem_of_ne_placeInfty K hv (Polynomial.X ^ n)
  rwa [map_pow, RatFunc.algebraMap_X] at h

theorem pow_X_mul_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ)
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    (RatFunc.X : RatFunc K) ^ n * g ∈ v.toValuationSubring :=
  mul_mem (pow_X_mem_of_ne_placeInfty K hv n) hg

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The coefficient of the given differential is integral at every finite place. -/
def P1DifferentialCoeffRegularFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K →
    v.differentialCoeff ω₀ ∈ v.toValuationSubring

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
theorem exists_monic_irreducible_factorization {d : K[X]} (hd : d.Monic) :
    ∃ (s : Finset K[X]) (n : K[X] → ℕ),
      (∀ p ∈ s, p.Monic) ∧ (∀ p ∈ s, Irreducible p) ∧
      (Set.Pairwise (s : Set K[X]) fun i j => IsCoprime i j) ∧
      d = ∏ p ∈ s, p ^ n p := by
  classical
  refine ⟨(normalizedFactors d).toFinset,
    fun p => (normalizedFactors d).count p, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff hd.ne_zero).mp
      (Multiset.mem_toFinset.mp hp)).2.1
  · intro p hp
    exact irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  · intro p hp q hq hne
    have hp' := Multiset.mem_toFinset.mp hp
    have hq' := Multiset.mem_toFinset.mp hq
    rw [(irreducible_of_normalized_factor p hp').coprime_iff_not_dvd]
    exact fun hdvd => hne (normalizedFactors_eq_of_dvd d p hp' q hq' hdvd)
  · calc d = (normalizedFactors d).prod := by
            rw [prod_normalizedFactors_eq hd.ne_zero, hd.normalize_eq_self]
      _ = ∏ p ∈ (normalizedFactors d).toFinset, p ^ (normalizedFactors d).count p :=
            Finset.prod_multiset_count _

theorem algebraMap_mem_span_P1PartialFractionGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PartialFractionGenerators K) :=
  Submodule.span_mono Set.subset_union_left
    (algebraMap_polynomial_mem_span_P1PolynomialGenerators q)

theorem div_pow_mem_span_P1PartialFractionGenerators
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) {m : ℕ} (hm : 1 ≤ m) :
    algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
      ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  exact Submodule.subset_span (Or.inr ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩)

theorem ratFunc_mem_span_P1PartialFractionGenerators (f : RatFunc K) :
    f ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  classical
  have hdenmon : f.denom.Monic := RatFunc.monic_denom f
  obtain ⟨s, n, hmon, hirr, hcop, hdfac⟩ :=
    exists_monic_irreducible_factorization hdenmon
  have hginv : ∀ p ∈ s,
      (algebraMap K[X] (RatFunc K) p)⁻¹ * algebraMap K[X] (RatFunc K) p = 1 :=
    fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hmon p hp).ne_zero)
  obtain ⟨q, r, hr, hpfrac⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) f.num hmon hcop n hginv
  have hLHS : algebraMap K[X] (RatFunc K) f.num *
      ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p = f := by
    have hprod : ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p
        = (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
      rw [hdfac, map_prod]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => by rw [map_pow, inv_pow]
    rw [hprod, ← div_eq_mul_inv, RatFunc.num_div_denom]
  rw [← hLHS, hpfrac]
  refine Submodule.add_mem _ (algebraMap_mem_span_P1PartialFractionGenerators q) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [inv_pow, ← div_eq_mul_inv]
  exact div_pow_mem_span_P1PartialFractionGenerators (hmon p hp) (hirr p hp)
    (hr p hp j) j.succ_pos

theorem p1PartialFractionSpan_eq_top :
    Submodule.span K (P1PartialFractionGenerators K) = ⊤ :=
  Submodule.eq_top_iff'.mpr ratFunc_mem_span_P1PartialFractionGenerators

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
omit [DecidableEq (RatFunc K)] in
theorem ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne
    (w : HeightOneSpectrum K[X]) {p : K[X]} (hp : Irreducible p)
    (hne : w ≠ heightOneSpectrumOfIrreducible K hp) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 0 := by
  by_contra hord
  refine hne (HeightOneSpectrum.ext ?_)
  have hmem : p ∈ w.asIdeal :=
    (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp.ne_zero).mp hord
  exact ((PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le
    (w.isPrime.isMaximal w.ne_bot).ne_top
    ((Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem)).symm

theorem ord_algebraMap_irreducible_eq_zero_of_ne
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) :
    v.ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · refine ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne K w hp ?_
    rintro rfl; exact hvp rfl
  · exact absurd rfl hvinf

theorem inv_algebraMap_pow_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) (m : ℕ) :
    ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹ ∈ v.toValuationSubring := by
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
  refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero m hp0)) ?_
  rw [v.ord_inv, ← zpow_natCast, v.ord_zpow,
    ord_algebraMap_irreducible_eq_zero_of_ne K hp hvp hvinf, mul_zero, _root_.neg_zero]

theorem p1PrincipalPartAtom_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) :
    p1PrincipalPartAtom K p c m ∈ v.toValuationSubring := by
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv]
  exact mul_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hvinf c)
    (inv_algebraMap_pow_mem_of_ne_finitePlace K hp hvp hvinf m)

theorem two_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 2 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [Nontrivial Ω[(RatFunc K)⁄K]] [HasPrincipalDivisors K (RatFunc K)] in
theorem p1DifferentialCoeffRegularFinite_of_unitFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : P1DifferentialCoeffUnitFinite K hω₀) :
    P1DifferentialCoeffRegularFinite K hω₀ :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero hω₀) (hunit v hv).ge

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_smul_left (g : F) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) :
    kaehlerResidueTerm (g • ω) α v = kaehlerResidueTerm ω (mulAdele K g α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

theorem weilSmul_weilOfKaehler [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) :
    weilSmul K F g (weilOfKaehler K F hω) = weilOfKaehler K F hgω := by
  refine LinearMap.ext fun α => ?_
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  exact finsum_congr fun v => (kaehlerResidueTerm_smul_left g ω α v).symm

theorem weilOfKaehler_smul_diagonal [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehler K F hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehler K F hω ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [← weilSmul_weilOfKaehler hω hgω, weilSmul_apply]
  exact congrArg _ (Subtype.ext (funext fun v => by
    simp only [adeleSpaceMul_coe, mulAdele_apply, diagonalHom_apply]))

theorem residueTheorem_iff_of_ne_zero (v : Place K F) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    (∀ [HasPrincipalDivisors K F], ResidueTheorem K F) ↔
      ∀ [HasPrincipalDivisors K F], ∀ f : F,
        weilOfKaehler K F hω₀ ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 := by
  constructor
  · intro hRT _ f; exact hRT hω₀ f
  · intro hsingle _ ω hω f
    obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero v hω hω₀
    rw [weilOfKaehler_smul_diagonal hω₀ hω f]
    exact hsingle (g * f)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

variable (K F) in
/-- The Weil functional of a nonzero differential evaluated on principal adeles. -/
def kaehlerResidueFunctional {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehler K F hω).comp (principalAdele K F)

variable (K F) in
/-- The linear subspace of rational functions with vanishing total residue. -/
def kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Submodule K F :=
  LinearMap.ker (kaehlerResidueFunctional K F hω)

theorem mem_kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ weilOfKaehler K F hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 :=
  Iff.rfl

theorem residueTheorem_iff_kaehlerResidueKernel_eq_top (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ResidueTheorem K F ↔ kaehlerResidueKernel K F hω₀ = ⊤ := by
  rw [Submodule.eq_top_iff']
  constructor
  · intro h f
    exact (mem_kaehlerResidueKernel hω₀).mpr (h hω₀ f)
  · intro h
    have hsingle : ∀ [HasPrincipalDivisors K F] (f : F),
        weilOfKaehler K F hω₀ ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 := by
      intro _ f
      exact (mem_kaehlerResidueKernel hω₀).mp (h f)
    intro ω hω f
    exact (residueTheorem_iff_of_ne_zero v hω₀).mpr hsingle hω f

theorem residueTheorem_of_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S : Set F}
    (hspan : Submodule.span K S = ⊤) (hS : S ⊆ kaehlerResidueKernel K F hω₀) :
    ResidueTheorem K F := by
  rw [residueTheorem_iff_kaehlerResidueKernel_eq_top v hω₀]
  exact top_unique (hspan ▸ Submodule.span_le.mpr hS)

omit [HasPrincipalDivisors K F] in
theorem residueTheorem_of_union_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S₁ S₂ : Set F} :
    ∀ [HasPrincipalDivisors K F],
      Submodule.span K (S₁ ∪ S₂) = ⊤ →
      S₁ ⊆ kaehlerResidueKernel K F hω₀ →
      S₂ ⊆ kaehlerResidueKernel K F hω₀ →
      ResidueTheorem K F := by
  intro _ hspan hS₁ hS₂
  exact residueTheorem_of_span_le_kernel v hω₀ hspan (Set.union_subset hS₁ hS₂)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- Polynomial monomials and irreducible principal parts span the rational function field. -/
def P1PartialFractionSpan : Prop :=
  Submodule.span K (P1PartialFractionGenerators K) = ⊤

/-- Every polynomial monomial lies in the total-residue kernel. -/
def P1ResiduePolynomialPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PolynomialGenerators K ⊆ kaehlerResidueKernel K (RatFunc K) hω₀

/-- Every irreducible principal part lies in the total-residue kernel. -/
def P1ResiduePrincipalPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PrincipalPartGenerators K ⊆ kaehlerResidueKernel K (RatFunc K) hω₀

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_partialFractions (v : Place K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) :
    ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PartialFractionSpan K →
      P1ResiduePolynomialPart K hω₀ →
      P1ResiduePrincipalPart K hω₀ →
      ResidueTheorem K (RatFunc K) := by
  intro _ hspan hpoly hprin
  exact residueTheorem_of_union_span_le_kernel v hω₀ hspan hpoly hprin

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
theorem residueTheorem_ratFunc_of_generators_residue
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    (v : Place K (RatFunc K)) {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) :
    ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1ResiduePolynomialPart K hω₀ → P1ResiduePrincipalPart K hω₀ →
      ResidueTheorem K (RatFunc K) := by
  intro _ hpoly hprin
  exact residueTheorem_ratFunc_of_partialFractions v hω₀ p1PartialFractionSpan_eq_top hpoly hprin

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

theorem mem_kaehlerResidueKernel_iff_finsum {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ ∑ᶠ v, kaehlerResidueTerm ω (diagonalHom K F f) v = 0 :=
  Iff.rfl

theorem mem_kaehlerResidueKernel_of_term_zero_compl {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  rw [mem_kaehlerResidueKernel_iff_finsum hω,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem mem_kaehlerResidueKernel_of_singleton {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTerm ω (diagonalHom K F f) v₀ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa only [Finset.mem_singleton] using hv)
  · simpa only [Finset.sum_singleton] using hv₀

theorem mem_kaehlerResidueKernel_of_pair {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTerm ω (diagonalHom K F f) v₀
      + kaehlerResidueTerm ω (diagonalHom K F f) v₁ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  classical
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]; exact hsum

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- Each polynomial monomial times the given differential has residue zero at infinity. -/
def P1PolynomialResidueAtInfinity {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ n : ℕ, kaehlerResidueTerm ω₀
    (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (placeInfty K) = 0

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
theorem p1ResiduePolynomialPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀) :
    P1ResiduePolynomialPart K hω₀ := by
  rintro _ ⟨n, rfl⟩
  refine mem_kaehlerResidueKernel_of_singleton hω₀ (v₀ := placeInfty K) ?_ (hinf n)
  intro v hv
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem (pow_X_mul_mem_of_ne_placeInfty K hv n (hreg v hv)))

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- A principal part contributes no residue away from its finite pole and infinity. -/
def P1PrincipalPartTermZeroOffSupport {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    ∀ v : Place K (RatFunc K), v ≠ finitePlace K hpirr → v ≠ placeInfty K →
      kaehlerResidueTerm ω₀
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0

/-- The residue terms at the finite pole and at infinity cancel for every principal part. -/
def P1PrincipalPartTwoPlaceCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
          (placeInfty K)
      = 0

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
theorem p1ResiduePrincipalPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    P1ResiduePrincipalPart K hω₀ := by
  rintro _ ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩
  exact mem_kaehlerResidueKernel_of_pair hω₀ (finitePlace_ne_placeInfty hpirr)
    (hoff p c m hpmon hpirr hdeg hm) (hcancel p c m hpmon hpirr hdeg hm)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_four_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ∀ [HasPrincipalDivisors K (RatFunc K)], ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_generators_residue (placeInfty K) hω₀
    (p1ResiduePolynomialPart_of_subrows hω₀ hreg hinf)
    (p1ResiduePrincipalPart_of_subrows hω₀ hoff hcancel)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [HasCanonicalDivisor (K := K) (F := RatFunc K)] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
  [Nontrivial Ω[(RatFunc K)⁄K]] [HasPrincipalDivisors K (RatFunc K)] in
theorem p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀) :
    P1PrincipalPartTermZeroOffSupport K hω₀ := by
  intro p c m _hpmon hpirr _hdeg _hm v hvp hvinf
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf) (hreg v hvinf)))

omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_three_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ∀ [HasPrincipalDivisors K (RatFunc K)], ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_four_subrows hω₀ hreg hinf
    (p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite K hω₀ hreg) hcancel

/-- The given differential has order minus two at infinity. -/
def P1OrdDifferentialPlaceInftyEqNegTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  (placeInfty K).ordDifferential ω₀ = -2

/-- The residue terms at the finite pole and infinity cancel for a simple principal part. -/
def P1PrincipalPartTwoPlaceCancelMOne {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
          (placeInfty K)
      = 0

omit [HasCanonicalDivisor (K := K) (F := RatFunc K)] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (placeInfty K) = 0 := by
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff ω₀ = 0
    rw [map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    have hd0 : (placeInfty K).differentialCoeff ω₀ ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero hω₀
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff ω₀) = -2 := hInfty
    omega

/-- Principal parts with denominator exponent at least two have zero finite-place residue. -/
def P1FinitePlaceTermZeroMGeTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (finitePlace K hpirr) = 0

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasCanonicalDivisor (K := K) (F := RatFunc K)] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem p1PrincipalPartTwoPlaceCancel_of_mOne
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K hω₀)
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K hω₀)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀) :
    P1PrincipalPartTwoPlaceCancel K hω₀ := by
  intro p c m hpmon hpirr hdeg hm
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact hMOne p c hpmon hpirr hdeg
  · rw [hMGeTwo p c m hpmon hpirr hdeg h2,
      kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m K hω₀ hInfty hpirr c hdeg h2, add_zero]

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) ≠ 0 := by
  classical
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv K, smul_ne_zero_iff]
  exact ⟨neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero), D_ratFuncX_inv_ne_zero K hwd⟩

theorem p1OrdDifferentialPlaceInftyEqNegTwo_D_X
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [HasPrincipalDivisors K (RatFunc K)]
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    P1OrdDifferentialPlaceInftyEqNegTwo K (D_ratFuncX_ne_zero K hwd) :=
  ordDifferential_placeInfty_D_ratFuncX K hwd

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [CharZero K] in
theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K))
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K)) :
    P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) :=
  p1PrincipalPartTwoPlaceCancel_of_mOne (dX_ne_zero K) hMOne hMGeTwo
    (p1OrdDifferentialPlaceInftyEqNegTwo_D_X K hwd)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
variable [PerfectField K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  p1DifferentialCoeffRegularFinite_of_unitFinite (dX_ne_zero K)
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem residueTheorem_ratFunc_of_two_subrows_of_perfectField
    : ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PolynomialResidueAtInfinity K (dX_ne_zero K) →
      P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) →
      ResidueTheorem K (RatFunc K) := by
  intro _ hinf hcancel
  exact residueTheorem_ratFunc_of_three_subrows K (dX_ne_zero K)
    (p1DifferentialCoeffRegularFinite_dX_of_perfectField K) hinf hcancel

theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField
    : ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) →
      P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K) →
      P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) := by
  intro _ hMOne hMGeTwo
  exact p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hMOne hMGeTwo

end
end AlgebraicCurve

noncomputable section

open _root_.AlgebraicCurves.Differentials.Residues.Proofs in
open _root_.AlgebraicCurve in
open _root_.AlgebraicCurve.RationalFunctionField in
open RatFuncResidue.AlgebraicCurve in
open _root_.Polynomial in
theorem _root_.AlgebraicCurve.residueTheorem_ratFunc_of_perfectField
    (K : Type*) [Field K] [PerfectField K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] :
    AlgebraicCurve.ResidueTheorem K (RatFunc K) := by
  classical
  have hinf : P1PolynomialResidueAtInfinity K (dX_ne_zero K) := by
    intro n
    simp only [kaehlerResidueTerm, diagonalHom_apply]
    exact AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero K n
  have hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) := by
    intro p c hmon hpirr hdeg
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom, pow_one]
    exact trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
      K hmon hpirr hdeg
  have hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K) := by
    intro p c m hmon hpirr hdeg hm
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom]
    exact AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero K
      hmon hpirr hdeg hm
  intro ω hω f
  exact residueTheorem_ratFunc_of_two_subrows_of_perfectField K hinf
    (p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField K hMOne hMGeTwo) hω f

end

end AlgebraicCurves.Differentials.Residues.Proofs.RatFuncResidue
