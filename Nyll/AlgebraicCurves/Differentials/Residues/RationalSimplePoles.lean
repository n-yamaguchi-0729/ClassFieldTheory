/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Residues.Construction
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Places.Rational.Differentials
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Rational.FiniteOrder
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Minpoly.MinpolyDiv
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Simple-pole residues on the rational function field

The finite-place Euler trace and the coefficient at infinity give cancellation for a simple
principal part. Local residues, places, and differential integrality use the shared constructions.
-/

namespace AlgebraicCurves.Differentials.Residues.Proofs.RationalSimplePoles
namespace AlgebraicCurve.RationalFunctionField
end AlgebraicCurve.RationalFunctionField
namespace FLT.EulerDualBasis
end FLT.EulerDualBasis
end AlgebraicCurves.Differentials.Residues.Proofs.RationalSimplePoles

namespace AlgebraicCurves.Differentials.Residues.Proofs.RationalSimplePoles

open _root_.IsDedekindDomain _root_.WithZero _root_.Module _root_.IsLocalRing
open _root_.Module.IsLocalRing _root_.KaehlerDifferential _root_.Polynomial _root_.Algebra
open _root_.AlgebraicCurve _root_.AlgebraicCurve.RationalFunctionField
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

namespace FLT.EulerDualBasis
noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem coeff_minpolyDiv_dim_sub_one (pb : PowerBasis K L) :
    (minpolyDiv K pb.gen).coeff (pb.dim - 1) = 1 := by
  have h1 : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by
    rw [natDegree_minpolyDiv, pb.natDegree_minpoly]
  rw [← h1]
  exact (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree

theorem traceDual_eq_one_div_of_val_eq (pb : PowerBasis K L) {j : Fin pb.dim}
    (hj : (j : ℕ) = pb.dim - 1) :
    pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
  rw [Module.Basis.traceDual_powerBasis_eq]
  rw [hj, coeff_minpolyDiv_dim_sub_one]

theorem trace_pow_div_aeval_derivative_minpoly_of_lt (pb : PowerBasis K L) {k : ℕ}
    (hk : k < pb.dim - 1) :
    Algebra.trace K L
      (pb.gen ^ k / aeval pb.gen (derivative (minpoly K pb.gen))) = 0 := by
  have hd : 0 < pb.dim := by omega
  have hk' : k < pb.dim := by omega
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨k, hk'⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, ite_eq_right]
  simp only [Fin.mk.injEq]
  omega

theorem trace_pow_div_aeval_derivative_minpoly_self (pb : PowerBasis K L)
    (hd : 0 < pb.dim) :
    Algebra.trace K L
      (pb.gen ^ (pb.dim - 1) / aeval pb.gen (derivative (minpoly K pb.gen))) = 1 := by
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨pb.dim - 1, hlt⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, ite_eq_left rfl]

end
end FLT.EulerDualBasis

namespace AlgebraicCurve
noncomputable section

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
variable (K F)

/-- Differentials of uniformizers at a place differ by a unit of order zero. -/
def OrdDifferentialWellDefined : Prop :=
  ∀ (v : Place K F) (π π' : F), v.ord π = 1 → v.ord π' = 1 →
    ∃ u : F, v.ord u = 0 ∧
      KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F :=
  RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The rational principal part with numerator c and denominator the m-th power of p. -/
abbrev p1PrincipalPartAtom (p c : K[X]) (m : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F :=
  RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] [HasPrincipalDivisors
  K (RatFunc K)] in
theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp ≠ placeInfty K :=
  fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

end
end AlgebraicCurve

namespace AlgebraicCurve.RationalFunctionField
noncomputable section

variable (K : Type*) [Field K]
theorem ord_finitePlace_self {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) = 1 := by
  rw [finitePlace_def]
  exact ord_ofHeightOneSpectrum_of_span
    (heightOneSpectrumOfIrreducible K hp) hp.ne_zero
    (heightOneSpectrumOfIrreducible_asIdeal K hp)

end
end AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem localResidueData_uniformizer_inv (v : Place K F) (R : v.LocalResidueData) :
    R.res v.uniformizer⁻¹ = 1 := by
  rw [v.localResidueData_res_eq_simplePoleResidueAux R
      (uniformizer_inv_mem_simplePoleSubmodule v).1,
    Place.simplePoleResidueAux_apply]
  have h1 :
      (⟨v.uniformizer * v.uniformizer⁻¹,
        (uniformizer_inv_mem_simplePoleSubmodule v).1⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

theorem ord_placeInfty_X_inv : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(placeInfty K).ord_inv, ord_placeInfty_X, neg_neg]

theorem ord_placeInfty_X_pow (n : ℕ) :
    (placeInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (placeInfty K).ord_zpow, ord_placeInfty_X]
  ring

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  classical
  obtain ⟨u, -, hueq⟩ :=
    hwd (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (placeInfty K).uniformizer
      (ord_placeInfty_X_inv K) (placeInfty K).ord_uniformizer
  intro h0
  refine (placeInfty K).dCoord_ne_zero ?_
  change KaehlerDifferential.D K (RatFunc K) (placeInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]

theorem differentialCoeff_placeInfty_D_X_eq :
    (placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (placeInfty K).differentialCoeff_smul]

theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ord
        ((placeInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (placeInfty K) (placeInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (placeInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(placeInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (placeInfty K).dCoord from hueq), hu0]

theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (placeInfty K).ord_neg,
    (placeInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((placeInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem canonicalLocalResidueDataK_uniformizer_inv (v : Place K F)
    (R : v.CanonicalLocalResidueDataK) : R.res v.uniformizer⁻¹ = 1 :=
  localResidueData_uniformizer_inv v R.toLocalResidueData

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
/-- The differential of the standard coordinate on the rational function field. -/
abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [_root_.eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  · exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
variable {K}
theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_
  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by rw [h, mul_zero])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
variable {K}
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.denom) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := (v).uniformizer_ne_zero
  by_contra hne
  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hordπ
  omega

theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.num) = 1 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := (v).uniformizer_ne_zero
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ ((v).uniformizer.num.derivative * (v).uniformizer.denom
            - (v).uniformizer.num * (v).uniformizer.denom.derivative) := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := (v).uniformizer_ne_zero
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd
  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
variable {K}
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).ord ((v).differentialCoeff (dX K)) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := (v).uniformizer_ne_zero
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hcoord : (v).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)
  have hcoeff : (v).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine (v).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]
  have hordξ : (v).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, (v).ord_inv, div_eq_mul_inv,
    (v).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, (v).ord_inv, ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
theorem ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0) (m : ℕ) :
    (placeInfty K).ord (p1PrincipalPartAtom K p c m)
      = (m : ℤ) * p.natDegree - c.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (placeInfty K).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (placeInfty K).ord_inv, ← zpow_natCast, (placeInfty K).ord_zpow,
    ord_placeInfty_algebraMap (K := K) hc, ord_placeInfty_algebraMap (K := K) hp]
  ring

theorem one_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    1 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 1 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

omit [DecidableEq (RatFunc K)] in
theorem not_dvd_of_degree_lt {p c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) : ¬ p ∣ c :=
  fun hdvd => not_lt.mpr (Polynomial.degree_le_of_dvd hdvd hc) hdeg

omit [DecidableEq (RatFunc K)] in
theorem ord_finitePlace_of_degree_lt {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) c) = 0 :=
  not_ne_iff.mp fun h =>
    not_dvd_of_degree_lt K hc hdeg
      ((_root_.AlgebraicCurve.RationalFunctionField.ord_finitePlace_ne_zero_iff K hp hc).mp h)

omit [DecidableEq (RatFunc K)] in
theorem ord_finitePlace_p1PrincipalPartAtom {p : K[X]} (hp : Irreducible p)
    {c : K[X]} (hc : c ≠ 0) (hdeg : c.degree < p.degree) (m : ℕ) :
    (finitePlace K hp).ord (p1PrincipalPartAtom K p c m) = -(m : ℤ) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (finitePlace K hp).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (finitePlace K hp).ord_inv, ← zpow_natCast, (finitePlace K hp).ord_zpow,
    ord_finitePlace_of_degree_lt K hp hc hdeg, ord_finitePlace_self K hp]
  ring

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F :=
  RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The coefficient of the given differential has order zero at every finite place. -/
def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  have : IsCurveOver K (RatFunc K) := _root_.AlgebraicCurve.instIsCurveOverRatFunc K
  have : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  have : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K K[X] (RatFunc K)
  exact fun v π π' hπ hπ' =>
    exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver v π π' hπ hπ'

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
theorem ord_finitePlace_mOneAtom_mul_differentialCoeff
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord
        (p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀) = -1 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(finitePlace K hp).ord_mul hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀),
    ord_finitePlace_p1PrincipalPartAtom K hp hc hdeg 1,
    hunit (finitePlace K hp) (finitePlace_ne_placeInfty hp)]
  norm_num

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (placeInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    -1 ≤ (placeInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀) := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(placeInfty K).ord_mul hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀)]
  have h1 : 1 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c 1) :=
    one_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg le_rfl
  have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff ω₀) = -2 := hInfty
  omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀
      ∈ (finitePlace K hp).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (finitePlace K hp).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (finitePlace K hp).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (finitePlace K hp).mem_of_ord_nonneg
      (mul_ne_zero (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀))) ?_
    rw [(finitePlace K hp).ord_mul (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀)),
      (finitePlace K hp).ord_uniformizer,
      ord_finitePlace_mOneAtom_mul_differentialCoeff K hω₀ hunit hp hc hdeg]
    omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (placeInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀
      ∈ (placeInfty K).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (placeInfty K).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (placeInfty K).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (placeInfty K).mem_of_ord_nonneg
      (mul_ne_zero (placeInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀))) ?_
    rw [(placeInfty K).ord_mul (placeInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero hω₀)),
      (placeInfty K).ord_uniformizer]
    have h := ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one K hω₀ hInfty hp hc hdeg
    omega

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
/-- The traced simple-pole residues at the finite place and at infinity sum to zero. -/
def P1PrincipalPartMOneSimplePoleCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff ω₀
        ∈ (finitePlace K hpirr).simplePoleSubmodule)
      (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω₀
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      + Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = 0

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable {p : K[X]} (hpirr : Irreducible p)
/-- The quotient by an irreducible polynomial identifies with the corresponding residue field. -/
def finitePlaceResidueFieldAlgEquivAdjoinRoot :
    AdjoinRoot p ≃ₐ[K] (finitePlace K hpirr).ResidueField :=
  residueFieldEquivOfHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hpirr)

omit [DecidableEq (RatFunc K)] in
theorem finitePlaceResidueFieldAlgEquivAdjoinRoot_mk (q : K[X]) :
    finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr (AdjoinRoot.mk p q)
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) q,
          algebraMap_mem_ofHeightOneSpectrum K _ q⟩ :=
  rfl

omit [DecidableEq (RatFunc K)] in
theorem trace_finitePlace_residueField_eq_trace_adjoinRoot
    (y : (finitePlace K hpirr).ResidueField) :
    Algebra.trace K (finitePlace K hpirr).ResidueField y
      = Algebra.trace K (AdjoinRoot p)
          ((finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm y) := by
  conv_lhs => rw [← (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).apply_symm_apply y]
  exact Algebra.trace_eq_of_algEquiv _ _

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
/-- The finite-place residue of c / p times dX is c(root) / p.derivative(root). -/
def P1FinitePlaceSimplePoleResidueAdjoinRootValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    let : Fact (Irreducible p) := ⟨hpirr⟩
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule),
    (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p)

/--
The traced residue of c / p times dX at infinity is minus the coefficient in degree deg(p) - 1.
-/
def P1PlaceInftySimplePoleResidueEulerValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c.degree < p.degree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

end
end AlgebraicCurve

namespace AlgebraicCurve.Place
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (v : Place K F)

omit [HasCanonicalLocalResidueKStar K F] in
private theorem _root_.AlgebraicCurve.Place.simplePoleResidueAux_mul_of_mem {a : F} (ha :
  a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule)
    (haf : a * f ∈ v.simplePoleSubmodule) :
    v.simplePoleResidueAux ⟨a * f, haf⟩
      = IsLocalRing.residue _ ⟨a, ha⟩ * v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [v.simplePoleResidueAux_apply, v.simplePoleResidueAux_apply, ← map_mul]
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (mul_left_comm _ _ _))

omit [HasCanonicalLocalResidueKStar K F] in
private theorem _root_.AlgebraicCurve.Place.mul_mem_simplePoleSubmodule_of_mem {a : F} (ha :
  a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    a * f ∈ v.simplePoleSubmodule := by
  rw [v.mem_simplePoleSubmodule, mul_left_comm]
  exact mul_mem ha hf

end
end AlgebraicCurve.Place

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K)
variable [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
omit [DecidableEq (RatFunc K)] in
theorem differentialCoeff_D_algebraMap_polynomial (v : Place K (RatFunc K)) (q : K[X]) :
    v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) q))
      = algebraMap K[X] (RatFunc K) q.derivative * v.differentialCoeff (dX K) := by
  rw [D_algebraMap_polynomial K q, v.differentialCoeff_smul]

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_dX
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hc : c ≠ 0) :
    (placeInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K))
      = (p.natDegree : ℤ) - c.natDegree - 2 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
  rw [(placeInfty K).ord_mul hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K)),
    ord_placeInfty_p1PrincipalPartAtom K hp hc 1, hInfty]
  push_cast; ring

theorem p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree) :
    p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).toValuationSubring := by
  rcases hcdeg with rfl | hcdeg
  · change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (placeInfty K).differentialCoeff (dX K) ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · rcases eq_or_ne c 0 with rfl | hc
    · change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K) ∈ _
      rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
    have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
    refine (placeInfty K).mem_of_ord_nonneg
      (mul_ne_zero hatom0 ((placeInfty K).differentialCoeff_ne_zero (dX_ne_zero K))) ?_
    rw [ord_placeInfty_mOneAtom_mul_differentialCoeff_dX K hInfty hp hc]
    omega

theorem trace_placeInfty_simplePoleResidue_mOne_of_lowDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hpirr : Irreducible p)
    (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree)
    (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1)) := by
  have hreg := p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hcdeg
  have hLHS : (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = 0 :=
    (placeInfty K).simplePoleResidueAux_eq_zero_of_mem hreg
  rw [hLHS, _root_.map_zero]
  rcases hcdeg with rfl | hcdeg
  · rw [coeff_zero, neg_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < p.natDegree - 1), _root_.neg_zero]

/-- The residue formula at infinity when the numerator has degree exactly deg(p) - 1. -/
def P1PlaceInftySimplePoleResidueEulerValueTopDeg : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c ≠ 0 → c.natDegree + 1 = p.natDegree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

/-- The traced residue of X^(deg(p) - 1) / p times dX at infinity is minus one. -/
def P1PlaceInftySimplePoleResidueEulerValueMonomial : Prop :=
  ∀ (p : K[X]) (_ : p.Monic) (_ : Irreducible p),
    ∀ (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

omit [DecidableEq (RatFunc K)] in
omit [∀ (v : Place K (RatFunc K)), v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem p1PrincipalPartAtom_add_mul_differentialCoeff (p c₁ c₂ : K[X]) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (c₁ + c₂) m * v.differentialCoeff ω
      = p1PrincipalPartAtom K p c₁ m * v.differentialCoeff ω
        + p1PrincipalPartAtom K p c₂ m * v.differentialCoeff ω := by
  change algebraMap K[X] (RatFunc K) (c₁ + c₂) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = algebraMap K[X] (RatFunc K) c₁ / (algebraMap K[X] (RatFunc K) p) ^ m * v.differentialCoeff ω
      + algebraMap K[X] (RatFunc K) c₂ / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
  rw [map_add]; ring

omit [DecidableEq (RatFunc K)] in
omit [∀ (v : Place K (RatFunc K)), v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem p1PrincipalPartAtom_C_mul_mul_differentialCoeff (p c : K[X]) (a : K) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (C a * c) m * v.differentialCoeff ω
      = a • (p1PrincipalPartAtom K p c m * v.differentialCoeff ω) := by
  change algebraMap K[X] (RatFunc K) (C a * c) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = a • (algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω)
  rw [map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
    Algebra.smul_def]
  ring

omit [∀ (v : Place K (RatFunc K)), v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem trace_placeInfty_simplePoleResidueAux_mOne_add
    {p c₁ c₂ : K[X]} {ω : Ω[(RatFunc K)⁄K]}
    (h1 : p1PrincipalPartAtom K p c₁ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h2 : p1PrincipalPartAtom K p c₂ 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (h12 : p1PrincipalPartAtom K p (c₁ + c₂) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, h12⟩)
      = Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, h1⟩)
        + Algebra.trace K (placeInfty K).ResidueField
            ((placeInfty K).simplePoleResidueAux ⟨_, h2⟩) := by
  have heq : (⟨_, h12⟩ : (placeInfty K).simplePoleSubmodule)
      = (⟨_, h1⟩ : (placeInfty K).simplePoleSubmodule) + ⟨_, h2⟩ :=
    Subtype.ext (p1PrincipalPartAtom_add_mul_differentialCoeff K p c₁ c₂ 1 _ ω)
  rw [heq, map_add, map_add]

omit [∀ (v : Place K (RatFunc K)), v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem trace_placeInfty_simplePoleResidueAux_mOne_C_mul
    {p c : K[X]} {a : K} {ω : Ω[(RatFunc K)⁄K]}
    (hc : p1PrincipalPartAtom K p c 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule)
    (hac : p1PrincipalPartAtom K p (C a * c) 1 * (placeInfty K).differentialCoeff ω
        ∈ (placeInfty K).simplePoleSubmodule) :
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, hac⟩)
      = a * Algebra.trace K (placeInfty K).ResidueField
          ((placeInfty K).simplePoleResidueAux ⟨_, hc⟩) := by
  have heq : (⟨_, hac⟩ : (placeInfty K).simplePoleSubmodule)
      = a • (⟨_, hc⟩ : (placeInfty K).simplePoleSubmodule) :=
    Subtype.ext (p1PrincipalPartAtom_C_mul_mul_differentialCoeff K p c a 1 _ ω)
  rw [heq, map_smul, map_smul, smul_eq_mul]

theorem p1PlaceInftySimplePoleResidueEulerValue_of_topDeg
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (htop : P1PlaceInftySimplePoleResidueEulerValueTopDeg K) :
    P1PlaceInftySimplePoleResidueEulerValue K := by
  intro p c hpmon hpirr hcdeg himem
  rcases eq_or_ne c 0 with rfl | hc
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inl rfl) himem
  have hndeg : c.natDegree < p.natDegree := natDegree_lt_natDegree hc hcdeg
  rcases (by omega : c.natDegree + 2 ≤ p.natDegree ∨ c.natDegree + 1 = p.natDegree) with h | h
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inr h) himem
  · exact htop p c hpmon hpirr hc h himem

theorem p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValueTopDeg K := by
  intro p c hpmon hpirr hc hcnd himem
  have hInfty' : (placeInfty K).ordDifferential (dX K) = -2 := hInfty
  have hXd : (X ^ (p.natDegree - 1) : K[X]).degree < p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpirr.ne_zero]
    exact_mod_cast (by omega : p.natDegree - 1 < p.natDegree)
  have hXmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) hInfty' hpirr (X ^ (p.natDegree - 1)) hXd
  have hCXmem : p1PrincipalPartAtom K p (C c.leadingCoeff * X ^ (p.natDegree - 1)) 1
        * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_C_mul_mul_differentialCoeff K]
    exact (placeInfty K).simplePoleSubmodule.smul_mem _ hXmem
  have hELdeg : c.eraseLead = 0 ∨ c.eraseLead.natDegree + 2 ≤ p.natDegree := by
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero c with h | h
    · exact .inr (by omega)
    · exact .inl h
  have hELmem : p1PrincipalPartAtom K p c.eraseLead 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mem_simplePoleSubmodule_of_mem
      (p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hELdeg)
  have hcnd' : c.natDegree = p.natDegree - 1 := by omega
  have hcdecomp : c = C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow c, add_comm, hcnd']
  have h12mem : p1PrincipalPartAtom K p
        (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead) 1
          * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_add_mul_differentialCoeff K]; exact add_mem hCXmem hELmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, h12mem⟩ := by
    refine Subtype.ext ?_
    change algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (placeInfty K).differentialCoeff (dX K)
      = algebraMap K[X] (RatFunc K) (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead)
          / (algebraMap K[X] (RatFunc K) p) ^ 1 * (placeInfty K).differentialCoeff (dX K)
    rw [← hcdecomp]
  have hELcoeff : c.eraseLead.coeff (p.natDegree - 1) = 0 := by
    rcases hELdeg with h | h
    · rw [h, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hLead : c.leadingCoeff = c.coeff (p.natDegree - 1) := by
    rw [leadingCoeff, hcnd']
  rw [heq, trace_placeInfty_simplePoleResidueAux_mOne_add K hCXmem hELmem,
    trace_placeInfty_simplePoleResidueAux_mOne_C_mul K hXmem,
    hmono p hpmon hpirr hXmem,
    trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr hELdeg hELmem,
    hELcoeff, _root_.neg_zero, add_zero, hLead]
  ring

theorem p1PlaceInftySimplePoleResidueEulerValue_of_monomial
    (hInfty : (placeInfty K).ord ((placeInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_topDeg K hInfty
    (p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial K hInfty hmono)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
theorem ord_placeInfty_X_pow_natDegree_div {p : K[X]} (hp : p ≠ 0) :
    (placeInfty K).ord
        (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd : (X ^ p.natDegree : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hXd
  rw [div_eq_mul_inv, (placeInfty K).ord_mul hXd' (inv_ne_zero hp'),
    (placeInfty K).ord_inv, ord_placeInfty_algebraMap (K := K) hXd,
    ord_placeInfty_algebraMap (K := K) hp,
    natDegree_X_pow]
  ring

theorem X_pow_natDegree_div_mem_placeInfty {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (pow_ne_zero _ X_ne_zero)
  exact (placeInfty K).mem_of_ord_nonneg (div_ne_zero hXd' hp')
    (ord_placeInfty_X_pow_natDegree_div K hp).ge

omit [DecidableEq (RatFunc K)] in
theorem degree_X_pow_natDegree_sub_lt_of_monic {p : K[X]} (hpmon : p.Monic) :
    ((X : K[X]) ^ p.natDegree - p).degree < p.degree := by
  have hdeg : ((X : K[X]) ^ p.natDegree).degree = p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpmon.ne_zero]
  refine (Polynomial.degree_sub_lt_left hdeg (pow_ne_zero _ X_ne_zero) ?_).trans_le hdeg.le
  rw [Polynomial.leadingCoeff_X_pow, hpmon]

theorem residue_placeInfty_X_pow_natDegree_div_monic_eq_one {p : K[X]} (hpmon : p.Monic) :
    IsLocalRing.residue _ ⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
      = (1 : (placeInfty K).ResidueField) := by
  rw [← sub_eq_zero, show (1 : (placeInfty K).ResidueField) = IsLocalRing.residue _ 1 from
      (map_one _).symm, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  set d := p.natDegree
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpmon.ne_zero
  have hsubmem : algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
      ∈ (placeInfty K).toValuationSubring := by
    rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
    · simp only [h0, _root_.map_zero, zero_div]; exact zero_mem _
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    refine (placeInfty K).mem_of_ord_nonneg (div_ne_zero h0' hp') ?_
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap (K := K) h0,
      ord_placeInfty_algebraMap (K := K) hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega
  have hcoe : (⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
        - 1 : (placeInfty K).toValuationSubring)
      = ⟨_, hsubmem⟩ := by
    refine Subtype.ext ?_
    change algebraMap K[X] (RatFunc K) (X ^ d) / algebraMap K[X] (RatFunc K) p - 1
      = algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
    rw [map_sub, sub_div, div_self hp']
  rw [hcoe, Place.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos]
  rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
  · exact .inl (by rw [h0, map_zero, zero_div])
  · refine .inr ?_
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    rw [div_eq_mul_inv, (placeInfty K).ord_mul h0' (inv_ne_zero hp'),
      (placeInfty K).ord_inv, ord_placeInfty_algebraMap (K := K) h0,
      ord_placeInfty_algebraMap (K := K) hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
/-- The traced residue of dX / X at infinity is minus one. -/
def P1PlaceInftySimplePoleResidueEulerValueX : Prop :=
  ∀ (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule),
    Algebra.trace K (placeInfty K).ResidueField
        ((placeInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [∀ (v : Place K (RatFunc K)),
  v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem p1MonomialAtom_eq_monicRatio_mul {p : K[X]} (hpdeg : 1 ≤ p.natDegree) :
    p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1 * (placeInfty K).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1
            * (placeInfty K).differentialCoeff (dX K)) := by
  change algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) / algebraMap K[X] (RatFunc K) p ^ 1
        * (placeInfty K).differentialCoeff (dX K)
    = algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
        * (algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
            * (placeInfty K).differentialCoeff (dX K))
  have hXd : algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
      = algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) * algebraMap K[X] (RatFunc K) X := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hpdeg]
  have hX0 : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr X_ne_zero
  rw [pow_one, pow_one, map_one, hXd, one_div]
  field_simp

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] in
theorem p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2) :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      ∈ (placeInfty K).simplePoleSubmodule :=
  p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K (dX_ne_zero K) hInfty
    irreducible_X 1 (by rw [degree_one, degree_X]; decide)

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] in
theorem simplePoleResidueAux_placeInfty_monomial_eq_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    {p : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩
      = (placeInfty K).simplePoleResidueAux
          ⟨_, p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty⟩ := by
  set hXmem := p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty
  have hfact := p1MonomialAtom_eq_monicRatio_mul K hpirr.natDegree_pos
  have hRatioMem := X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero
  have hprodmem : (algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
          / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K))
      ∈ (placeInfty K).simplePoleSubmodule :=
    (placeInfty K).mul_mem_simplePoleSubmodule_of_mem hRatioMem hXmem
  have heq : (⟨_, himem⟩ : (placeInfty K).simplePoleSubmodule) = ⟨_, hprodmem⟩ :=
    Subtype.ext hfact
  rw [heq, (placeInfty K).simplePoleResidueAux_mul_of_mem hRatioMem hXmem,
    residue_placeInfty_X_pow_natDegree_div_monic_eq_one K hpmon, one_mul]

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] in
theorem p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X
    (hInfty : (placeInfty K).ordDifferential (dX K) = -2)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K := by
  intro p hpmon hpirr himem
  rw [simplePoleResidueAux_placeInfty_monomial_eq_X K hInfty hpmon hpirr himem]
  exact hX _

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- Every uniformizer has logarithmic differential of residue one. -/
def CanonicalLocalResidueKSimplePoleCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK),
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K]
variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem p1XAtom_mul_differentialCoeff_dX_eq_neg :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹) := by
  change algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
        * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹)
  rw [show (dX K) = KaehlerDifferential.D K (RatFunc K) RatFunc.X from rfl,
    differentialCoeff_placeInfty_D_X_eq K, RatFunc.algebraMap_X, map_one, pow_one, inv_inv,
    one_div]
  field_simp [RatFunc.X_ne_zero (K := K), sq, mul_comm]

omit [∀ (v : Place K (RatFunc K)), v.DCoordGenerates] [Nontrivial Ω[RatFunc K⁄K]] in
theorem trace_placeInfty_residueField_one :
    Algebra.trace K (placeInfty K).ResidueField 1 = 1 := by
  rw [show (1 : (placeInfty K).ResidueField) = algebraMap K _ 1 from (map_one _).symm,
    Algebra.trace_algebraMap, show Module.finrank K (placeInfty K).ResidueField = 1 from
      deg_placeInfty K, one_smul]

theorem simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = -1 := by
  set R := (placeInfty K).canonicalLocalResidueDataKOfExtend
  rw [← (placeInfty K).localResidueData_res_eq_simplePoleResidueAux R.toLocalResidueData himem,
    show R.toLocalResidueData.res = R.res from rfl,
    p1XAtom_mul_differentialCoeff_dX_eq_neg K, _root_.map_neg,
    hsp (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R]

theorem p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PlaceInftySimplePoleResidueEulerValueX K := by
  intro himem
  rw [simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one K hsp himem, _root_.map_neg,
    trace_placeInfty_residueField_one K]

end
end AlgebraicCurve

namespace AlgebraicCurve.Place
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalLocalResidueKStar K F] in
open scoped _root_.AlgebraicCurve.Place.CanonicalLocalResidueDataK in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {π' : F} (hπ' : v.ord π' = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1 := by
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  set w : F := π' * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hπ'0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul hπ'0 (inv_ne_zero hπv0), v.ord_inv, hπ', v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega
  have hπ'_eq : π' = v.uniformizer * w := by
    rw [hw_def, mul_comm π' (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]
  have hD : KaehlerDifferential.D K F π'
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [hπ'_eq]
    exact Derivation.leibniz _ _ _
  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F π')
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, v.differentialCoeff_add, v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]
  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, hπ'_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, canonicalLocalResidueDataK_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end
end AlgebraicCurve.Place

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K]
variable [PerfectField K] [DecidableEq (RatFunc K)]
variable [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc
  K)⁄K]]
theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable {p : K[X]} [Fact (Irreducible p)]
omit [DecidableEq (RatFunc K)] in
theorem trace_root_pow_div_derivative_of_lt (hpmon : p.Monic)
    {k : ℕ} (hk : k < p.natDegree - 1) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p)) = 0 := by
  have : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hpmon.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

omit [DecidableEq (RatFunc K)] in
theorem trace_root_pow_div_derivative_self (hpmon : p.Monic)
    (hd : 0 < p.natDegree) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ (p.natDegree - 1) /
        aeval (AdjoinRoot.root p) (derivative p)) = 1 := by
  have : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hpmon.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

omit [PerfectField K] [DecidableEq (RatFunc K)] in
private theorem aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

omit [DecidableEq (RatFunc K)] in
theorem trace_adjoinRoot_mk_div_mk_derivative (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  have : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa only [Polynomial.natDegree_zero] using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]
  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (p.natDegree - 1)]
  · rw [trace_root_pow_div_derivative_self K hpmon hpd, mul_one]
  · intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [trace_root_pow_div_derivative_of_lt K hpmon hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc
  K)⁄K]]
omit [PerfectField K] [DecidableEq (RatFunc K)] in
omit [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
  [Nontrivial Ω[RatFunc K⁄K]] in
theorem uniformizer_div_polynomial_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

omit [PerfectField K] [DecidableEq (RatFunc K)] in
theorem uniformizer_div_polynomial_differential_remainder
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h
  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib,
      _root_.AlgebraicCurve.Place.differentialCoeff_add v,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

omit [DecidableEq (RatFunc K)] in
theorem uniformizer_div_polynomial_mul_differentialCoeff_D_mem
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  refine mul_mem (uniformizer_div_polynomial_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge)

omit [DecidableEq (RatFunc K)] in
theorem residue_uniformizer_div_polynomial_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _
        ⟨_, uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 from (map_one _).symm,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _)
      (uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr)
  have hcoe : (⟨_, uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_
  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    uniformizer_div_polynomial_differential_remainder K hpirr
  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    _root_.AlgebraicCurve.RationalFunctionField.differentialCoeff_D_mem
      (finitePlace K hpirr)
      (uniformizer_div_polynomial_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

omit [DecidableEq (RatFunc K)] in
omit [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
  [Nontrivial Ω[RatFunc K⁄K]] in
theorem residue_polynomial_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit
    ((PerfectField.separable_of_irreducible hpirr).isUnit_of_dvd' dvd_rfl hlt')

omit [DecidableEq (RatFunc K)] in
theorem simplePoleResidueAux_finitePlace_principalPart
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  rw [Place.simplePoleResidueAux_apply,
    eq_div_iff (residue_polynomial_derivative_ne_zero K hpirr)]
  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    change v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf
  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, uniformizer_div_polynomial_mul_differentialCoeff_D_mem K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [residue_uniformizer_div_polynomial_mul_differentialCoeff_D K hpirr, mul_one]

omit [DecidableEq (RatFunc K)] in
theorem finitePlace_simplePole_residue_adjoinRoot :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  let : Fact (Irreducible p) := ⟨hpirr⟩
  change ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
      ∈ (finitePlace K hpirr).simplePoleSubmodule),
    (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm
        ((finitePlace K hpirr).simplePoleResidueAux
          ⟨p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K), hfmem⟩)
      = AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p)
  intro hfmem
  rw [simplePoleResidueAux_finitePlace_principalPart K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

omit [DecidableEq (RatFunc K)] in
theorem trace_finitePlace_simplePoleResidue
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  have : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := finitePlace_simplePole_residue_adjoinRoot K
    p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    trace_adjoinRoot_mk_div_mk_derivative K hpmon hdeg]

theorem simplePole_residues_cancel_of_infty_coefficient
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) := by
  intro p c hpmon hpirr hdeg hfmem himem
  rw [trace_finitePlace_simplePoleResidue K
      hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [PerfectField K]
variable [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc
  K)⁄K]]
theorem simplePole_coordinate_independence_ratFunc :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R =>
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
      (fun _ hh => _root_.AlgebraicCurve.RationalFunctionField.differentialCoeff_D_mem v hh) R hπ'

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc
  K)⁄K]]
theorem placeInfty_simplePoleResidue_X :
    P1PlaceInftySimplePoleResidueEulerValueX K :=
  p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K
    (simplePole_coordinate_independence_ratFunc K)

theorem placeInfty_simplePoleResidue_monomial :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K :=
  p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (placeInfty_simplePoleResidue_X K)

theorem placeInfty_simplePoleResidue_coefficient :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (placeInfty_simplePoleResidue_monomial K)

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} {f : F} {v : Place K F}
    (hmem : f * v.differentialCoeff ω ∈ v.simplePoleSubmodule) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v
      = Algebra.trace K v.ResidueField
          (v.simplePoleResidueAux ⟨f * v.differentialCoeff ω, hmem⟩) := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply,
    (Rfam v).res_simplePole (f * v.differentialCoeff ω) hmem]
  rfl

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

end
end AlgebraicCurve

namespace AlgebraicCurve
noncomputable section

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]
variable [∀ v : _root_.AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc
  K)⁄K]]
omit [HasPrincipalDivisors K (RatFunc K)] in
theorem kaehlerResidueTermKFam_simplePole_pair_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (placeInfty K) = 0 := by
  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX_of_perfectField K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg
  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]
  exact simplePole_residues_cancel_of_infty_coefficient K
    (placeInfty_simplePoleResidue_coefficient K) p c hpmon hpirr hdeg hfmem himem

end
end AlgebraicCurve

end AlgebraicCurves.Differentials.Residues.Proofs.RationalSimplePoles
