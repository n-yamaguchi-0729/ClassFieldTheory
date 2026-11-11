/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.CountNormalizedFactorsSpanSingleton
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Nyll.AlgebraicCurves.FunctionFields.NormTrace.RelNormEqPowIsMaximal

/-!
# Place ord norm eq sum fiber Over of is Separable
-/

@[expose] public section

section ProofImplementation


namespace AlgebraicCurves.Places.Proofs.PlaceNormOrderSumSeparable

open _root_.AlgebraicCurves.Places.Proofs

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x :=
  _root_.AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w φ hmul hone hiff hx

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

private theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x :=
  _root_.AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord hw hx

private theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n :=
  _root_.AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw hc n

end ValuationDictionary

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

private def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.toValuationSubringOfRestrictEq hw

omit [FiniteDimensional F F'] in
@[scoped simp]
private theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_toValuationSubringOfRestrictEq hw c

private def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter hw

omit [FiniteDimensional F F'] in
private theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter_apply hw c

private theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.ker_residueOfCenter hw

private theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.surjective_residueOfCenter hw

private def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueFieldEquivQuotientCenter hw

private def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.placeCongrEquiv h
@[scoped simp]
private theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_placeCongrEquiv h x

private def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.restrictResidueFieldEquiv hw

private theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (fiberCenter F' v hw).asIdeal.inertiaDeg v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.inertiaDeg_eq_inertiaDeg_fiberCenter hw

end ResidueDictionary

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The order of an actual valuation-subring element whose principal ideal
is a maximal-ideal power. -/
theorem _root_.AlgebraicCurve.Place.ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal
    {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

end DVR

end Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section IdealNorm

variable {v : Place K F} {w : Place K F'}

/-- The relative norm of the actual height-one centre of an extending place. -/
theorem _root_.AlgebraicCurve.Place.relNorm_fiberCenter (hw : w.restrict F = v) :
    Ideal.relNorm v.toValuationSubring (fiberCenter F' v hw).asIdeal
      = IsLocalRing.maximalIdeal v.toValuationSubring ^ w.inertiaDeg F := by
  have : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have : (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hw
  rw [AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable F F' (fiberCenter F' v hw).asIdeal
    (IsLocalRing.maximalIdeal v.toValuationSubring), inertiaDeg_eq_inertiaDeg_fiberCenter hw]

private theorem count_normalizedFactors_span_singleton
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal
      = (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
  _root_.AlgebraicCurve.Place.count_normalizedFactors_span_singleton hw hc

private theorem relNorm_span_singleton {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt F' v)) ≠ ⊥ := by simpa using hc
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (Ideal.span {c})
    with hS
  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    have : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩
  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiberOver F').attach.image
    (fun w' => (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', (mem_fiberOver v).mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiberOver F'} =>
      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) (v.fiberOver F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq ((mem_fiberOver v).mp w₁.2) ((mem_fiberOver v).mp w₂.2)
      (HeightOneSpectrum.ext h))
  calc
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
        = Ideal.relNorm v.toValuationSubring (∏ Q ∈ S.toFinset, Q ^ S.count Q) := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hspan]
    _ = ∏ Q ∈ S.toFinset, Ideal.relNorm v.toValuationSubring Q ^ S.count Q := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun Q _ => map_pow _ Q _
    _ = ∏ Q ∈ S.toFinset, IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (Q.inertiaDeg v.toValuationSubring * S.count Q) := by
          refine Finset.prod_congr rfl fun Q hQ => ?_
          obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
          rw [relNorm_fiberCenter hw', ← pow_mul, inertiaDeg_eq_inertiaDeg_fiberCenter hw']
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ Q ∈ S.toFinset,
              Q.inertiaDeg v.toValuationSubring * S.count Q) :=
          Finset.prod_pow_eq_pow_sum S.toFinset
            (fun Q => Q.inertiaDeg v.toValuationSubring * S.count Q)
            (IsLocalRing.maximalIdeal v.toValuationSubring)
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
          congr 1
          calc
            ∑ Q ∈ S.toFinset,
                Q.inertiaDeg v.toValuationSubring * S.count Q
                = ∑ Q ∈ T,
                    Q.inertiaDeg v.toValuationSubring
                      * S.count Q := by
                  refine Finset.sum_subset hsub fun Q _ hQ => ?_
                  rw [Multiset.count_eq_zero_of_notMem
                    (fun h => hQ (Multiset.mem_toFinset.mpr h)), mul_zero]
            _ = ∑ w' ∈ (v.fiberOver F').attach,
                  (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal.inertiaDeg
                    v.toValuationSubring
                    * S.count (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal := by
                  rw [hT, Finset.sum_image hinj]
            _ = ∑ w' ∈ (v.fiberOver F').attach, (w'.1.inertiaDeg F
                  * (w'.1.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  rw [← inertiaDeg_eq_inertiaDeg_fiberCenter ((mem_fiberOver v).mp w'.2),
                    count_normalizedFactors_span_singleton ((mem_fiberOver v).mp w'.2) hc]
            _ = ∑ w ∈ v.fiberOver F',
                  w.inertiaDeg F
                    * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
                  Finset.sum_attach (v.fiberOver F') fun w =>
                    w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat

/-- The norm of the actual principal ideal, over all places above the base place. -/
theorem _root_.AlgebraicCurve.Place.relNorm_span_singleton_of_isSeparable
    {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) :=
  relNorm_span_singleton hc

end IdealNorm

section ElementNorm

variable (v : Place K F)

private theorem ord_norm_algebraMap_integralClosureAt
    {c : integralClosureAt F' v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt F' v) F' c))
      = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
          * w.ord (algebraMap (integralClosureAt F' v) F' c) := by
  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
    (B := integralClosureAt F' v)]
  have hrel := relNorm_span_singleton (v := v) hc
  rw [Ideal.relNorm_singleton] at hrel
  rw [ValuationSubring.algebraMap_apply, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal v hrel]
  push_cast
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Int.toNat_of_nonneg
    (w.ord_nonneg_of_mem (forall_mem_of_restrict_eq ((mem_fiberOver v).mp hw) c))]

theorem ord_norm_eq_sum_fiberOver_local {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsF : algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsF
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])
  have hintc := ord_norm_algebraMap_integralClosureAt v hc0
  have hints := ord_norm_algebraMap_integralClosureAt v hs0
  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsF), hints] at hintc
  have hsplit : ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
      * w.ord (f * algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
        = (∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f)
          + ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
              * w.ord (algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [w.ord_mul hf hsF]
    ring
  rw [hsplit] at hintc
  omega

end ElementNorm

end Place

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver_of_isSeparable {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F
  F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f :=
  PlaceNormOrderSumSeparable.AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver_local v hf
end
end AlgebraicCurves.Places.Proofs.PlaceNormOrderSumSeparable
end ProofImplementation
