/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Orders.PositiveOrderElement
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Places.Orders.MinpolyCoefficientOrder

/-!
# Place sum ramificationIndex mul inertiaDeg

Centres in the integral closure and their residue fields yield the ramification-index and inertia-
degree sum for a finite separable field extension.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg

attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.congrEquiv_apply
attribute [-simp] AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open _root_.AlgebraicCurve

noncomputable section

noncomputable section

open IsDedekindDomain Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

open _root_.AlgebraicCurve.Place

theorem exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 :=
  _root_.AlgebraicCurve.Place.exists_minpoly_coeff_ord_ne_zero (F := F) w hf hford

end SupportTransfer

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

/-- Restrict the chart coefficient map to the valuation subring. -/
def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[scoped simp]
private theorem coe_chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) (r : R) :
    (chartHom w hw r : F) = algebraMap R F r := rfl

variable (R) in
/-- The centre ideal obtained by pulling back the maximal ideal of the place. -/
def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

scoped instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem mem_center_iff (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) {r : R} :
    r ∈ center R w hw ↔
      (⟨algebraMap R F r, hw r⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring :=
  Iff.rfl

theorem mem_center_iff_ord_pos (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {r : R} (hr : r ≠ 0) :
    r ∈ center R w hw ↔ 0 < w.ord (algebraMap R F r) := by
  have hr' : algebraMap R F r ≠ 0 := by
    simpa using (IsFractionRing.injective R F).ne_iff.mpr hr
  rw [mem_center_iff, w.mem_maximalIdeal_iff_ord_pos hr']

omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

theorem center_ne_bot (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    center R w hw ≠ ⊥ := by
  intro hbot
  apply w.ne_top'
  have hunit : ∀ r : R, r ≠ 0 → IsUnit (chartHom w hw r) := by
    intro r hr
    by_contra hu
    have : r ∈ center R w hw :=
      (mem_center_iff w hw).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [hbot] at this
    exact hr (by simpa using this)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) x
  rw [← hx, div_eq_mul_inv]
  exact mul_mem (hw a) (inv_algebraMap_mem w hw (hunit b (nonZeroDivisors.ne_zero hb)))

variable (R) in
/-- The centre regarded as a height-one prime of the base ring. -/
def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, inferInstance, center_ne_bot w hw⟩
@[scoped simp]
theorem centerHeightOneSpectrum_asIdeal
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (centerHeightOneSpectrum R w hw).asIdeal = center R w hw := rfl

theorem valuationSubringAtPrime_centerHeightOneSpectrum_le
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) ≤
      w.toValuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  refine mul_mem (hw a) (inv_algebraMap_mem w hw ?_)
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hs ((mem_center_iff w hw).mpr hmem)

theorem toValuationSubring_eq_of_forall_mem
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_centerHeightOneSpectrum_le w hw) w.ne_top').symm

theorem finite_setOf_forall_mem_and_ord_pos {r₀ : R} (hr₀ : r₀ ≠ 0) :
    {w : Place K F | (∀ r : R, algebraMap R F r ∈ w.toValuationSubring) ∧
      0 < w.ord (algebraMap R F r₀)}.Finite := by
  have hfin : {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hr₀)
  rw [← Set.finite_coe_iff]
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun w => (⟨centerHeightOneSpectrum R w.1 w.2.1, ?_⟩ :
      {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}})) ?_
  · rw [Set.mem_ofPred_eq, centerHeightOneSpectrum_asIdeal, Ideal.dvd_span_singleton]
    exact (mem_center_iff_ord_pos w.1 w.2.1 hr₀).mpr w.2.2
  · intro w w' h
    have hcenter : centerHeightOneSpectrum R w.1 w.2.1
        = centerHeightOneSpectrum R w'.1 w'.2.1 := congrArg Subtype.val h
    refine Subtype.ext (Place.ext ?_)
    rw [toValuationSubring_eq_of_forall_mem w.1 w.2.1,
      toValuationSubring_eq_of_forall_mem w'.1 w'.2.1, hcenter]

end Chart

section FiberFiniteness

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem finite_setOf_restrict_eq (v : Place K F) :
    {w : Place K F' | w.restrict F = v}.Finite := by
  classical
  let : Algebra v.toValuationSubring F' :=
    ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra
  have : IsScalarTower v.toValuationSubring F F' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDedekindDomain (integralClosure v.toValuationSubring F') :=
    integralClosure.isDedekindDomain v.toValuationSubring F F'
  have : IsFractionRing (integralClosure v.toValuationSubring F') F' :=
    integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'
  obtain ⟨π, hπ0, hπpos⟩ := v.exists_ord_pos
  have hπmem : π ∈ v.toValuationSubring := v.mem_of_ord_nonneg hπ0 hπpos.le
  set C := integralClosure v.toValuationSubring F' with hC
  set π' : C := algebraMap v.toValuationSubring C ⟨π, hπmem⟩ with hπ'
  have hπ'F : algebraMap C F' π' = algebraMap F F' π := by
    rw [hπ', ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply
      v.toValuationSubring F F']
    rfl
  have hπ'0 : π' ≠ 0 := by
    intro h
    apply hπ0
    have : algebraMap C F' π' = 0 := by rw [h, map_zero]
    rw [hπ'F] at this
    simpa using this
  refine Set.Finite.subset (finite_setOf_forall_mem_and_ord_pos (R := C) hπ'0) ?_
  rintro w (hw : w.restrict F = v)
  have hOv : ∀ g : F, g ∈ v.toValuationSubring → algebraMap F F' g ∈ w.toValuationSubring := by
    intro g hg
    rw [← hw] at hg
    exact hg
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Q, hQmonic, hQeval⟩ := c.2
    have : algebraMap C F' c = (c : F') := rfl
    rw [this]
    refine w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap v.toValuationSubring F'))
      (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
    rw [Polynomial.coeff_map, IsScalarTower.algebraMap_apply v.toValuationSubring F F']
    exact hOv _ (Q.coeff i).2
  · rw [hπ'F, w.ord_restrict π, hw]
    have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    positivity

end FiberFiniteness

end Place

end AlgebraicCurve

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

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x :=
  _root_.AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w φ hmul hone hiff hx

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (F') in
/-- The valuation-subring algebra structure induced by the original field extension map. -/
@[reducible] def valuationSubringAlgebra (v : Place K F) : Algebra v.toValuationSubring F' :=
  ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (F') in
/-- The integral closure of the base place valuation subring in the extension field. -/
abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'

scoped instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

scoped instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

scoped instance : Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
theorem algebraMap_integralClosureAt_injective :
    Function.Injective
      (algebraMap v.toValuationSubring (integralClosureAt F' v)) := by
  intro a b hab
  have h1 : algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) a)
        = algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) b) := by rw [hab]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  exact ((algebraMap F F').injective.comp
    (IsFractionRing.injective v.toValuationSubring F)) h1

scoped instance : Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

theorem maximalIdeal_ne_bot :
    IsLocalRing.maximalIdeal v.toValuationSubring ≠ ⊥ := by
  intro h
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top'
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

omit [FiniteDimensional F F'] in
theorem forall_mem_of_restrict_eq (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring := by
  obtain ⟨Q, hQmonic, hQeval⟩ := c.2
  have hOv : ∀ g : F, g ∈ v.toValuationSubring →
      algebraMap F F' g ∈ w.toValuationSubring := by
    intro g hg
    rw [← hw] at hg
    exact hg
  refine w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap v.toValuationSubring F'))
    (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
  rw [Polynomial.coeff_map,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  exact hOv _ (Q.coeff i).2

variable (F' v) in
/-- The height-one centre of an extending place in the integral closure. -/
def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosureAt F' v) :=
  centerHeightOneSpectrum (integralClosureAt F' v) w (forall_mem_of_restrict_eq hw)

theorem mem_fiberCenter_iff_ord_pos (hw : w.restrict F = v) {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    c ∈ (fiberCenter F' v hw).asIdeal ↔
      0 < w.ord (algebraMap (integralClosureAt F' v) F' c) :=
  mem_center_iff_ord_pos w (forall_mem_of_restrict_eq hw) hc

theorem toValuationSubring_eq_of_restrict_eq (hw : w.restrict F = v) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) :=
  toValuationSubring_eq_of_forall_mem w (forall_mem_of_restrict_eq hw)

theorem mem_maximalIdeal_iff_ord_pos' {r : v.toValuationSubring} (hr : r ≠ 0) :
    r ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord (algebraMap v.toValuationSubring F r) := by
  have hrF : (algebraMap v.toValuationSubring F r : F) ≠ 0 := by
    simpa using (IsFractionRing.injective v.toValuationSubring F).ne_iff.mpr hr
  have := v.mem_maximalIdeal_iff_ord_pos hrF (Subtype.coe_prop r)
  simpa using this

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
theorem algebraMap_integralClosureAt_ne_zero {r : v.toValuationSubring} (hr : r ≠ 0) :
    algebraMap v.toValuationSubring (integralClosureAt F' v) r ≠ 0 := fun h =>
  hr (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))

omit [FiniteDimensional F F'] in
theorem ord_algebraMap_integralClosureAt (hw : w.restrict F = v) (r : v.toValuationSubring) :
    w.ord (algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) r))
      = w.ramificationIndex F * v.ord (algebraMap v.toValuationSubring F r) := by
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F', w.ord_restrict, hw]

theorem fiberCenter_liesOver (hw : w.restrict F = v) :
    (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := by
  refine ⟨?_⟩
  rw [Ideal.under_def]
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)
  rw [Ideal.mem_comap,
    mem_fiberCenter_iff_ord_pos hw (algebraMap_integralClosureAt_ne_zero hr),
    ord_algebraMap_integralClosureAt hw, mem_maximalIdeal_iff_ord_pos' hr]
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos
  constructor
  · intro h
    positivity
  · intro h
    rcases mul_pos_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · omega

end Center

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x :=
  _root_.AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord hw hx

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n :=
  _root_.AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw hc n

theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw

end ValuationDictionary

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

/-- The map from the integral closure to the valuation subring of the extending place. -/
def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.toValuationSubringOfRestrictEq hw

omit [FiniteDimensional F F'] in
@[scoped simp]
theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_toValuationSubringOfRestrictEq hw c

/-- The integral-closure map to the residue field of the extending place. -/
def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter hw

omit [FiniteDimensional F F'] in
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter_apply hw c

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.ker_residueOfCenter hw

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.surjective_residueOfCenter hw

/-- The quotient by the centre identified with the residue field of the extending place. -/
def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueFieldEquivQuotientCenter hw

theorem residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueFieldEquivQuotientCenter_mk hw c

/-- The valuation-subring equivalence induced by equality of two places. -/
def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.placeCongrEquiv h
@[scoped simp]
theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_placeCongrEquiv h x

/-- The residue-field equivalence induced by equality of the restricted and base places. -/
def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.restrictResidueFieldEquiv hw

omit [FiniteDimensional F F'] in
theorem restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (placeCongrEquiv hw a) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.restrictResidueFieldEquiv_residue hw a

theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (fiberCenter F' v hw).asIdeal.inertiaDeg v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.inertiaDeg_eq_inertiaDeg_fiberCenter hw

end ResidueDictionary

section Bijection

variable {v : Place K F}

/-- The extending place given by a height-one prime of the integral closure. -/
def placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) : Place K F' where
  toValuationSubring := HeightOneSpectrum.valuationSubringAtPrime F' P
  algebraMap_mem' := fun a => by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap K F' a = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v)
          (algebraMap K v.toValuationSubring a)) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F',
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
        ← IsScalarTower.algebraMap_apply K F F']
    rw [h1]
    exact P.valuation_le_one _
  ne_top' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact isPrincipalIdealRing_valuationSubring P
@[scoped simp]
theorem placeOfPrime_toValuationSubring (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).toValuationSubring = HeightOneSpectrum.valuationSubringAtPrime F' P :=
  rfl

theorem restrict_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).restrict F = v := by
  have hle : v.toValuationSubring ≤ ((placeOfPrime P).restrict F).toValuationSubring := by
    intro g hg
    rw [restrict_toValuationSubring, ValuationSubring.mem_comap,
      placeOfPrime_toValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap F F' g = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) ⟨g, hg⟩) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F']
      rfl
    rw [h1]
    exact P.valuation_le_one _
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle
    ((placeOfPrime P).restrict F).ne_top')).symm

theorem fiberCenter_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    fiberCenter F' v (restrict_placeOfPrime P) = P := by
  have h1 : HeightOneSpectrum.valuationSubringAtPrime F'
      (fiberCenter F' v (restrict_placeOfPrime P))
        = HeightOneSpectrum.valuationSubringAtPrime F' P := by
    rw [← toValuationSubring_eq_of_restrict_eq (restrict_placeOfPrime P),
      placeOfPrime_toValuationSubring]
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F') ?_
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, h1]

theorem eq_of_fiberCenter_eq {w w' : Place K F'} (hw : w.restrict F = v)
    (hw' : w'.restrict F = v)
    (h : fiberCenter F' v hw = fiberCenter F' v hw') : w = w' := by
  refine Place.ext ?_
  rw [toValuationSubring_eq_of_restrict_eq hw, toValuationSubring_eq_of_restrict_eq hw', h]

end Bijection

section Assembly

variable (v : Place K F)

theorem sum_ramificationIndex_mul_inertiaDeg_infra [HasPrincipalDivisors K F'] :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v)
  rw [← IsFractionRing.finrank_eq v.toValuationSubring F (integralClosureAt F' v) F'] at hkey
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => ⟨(fiberCenter F' v (Place.mem_fiber.mp hw)).asIdeal,
      (fiberCenter F' v (Place.mem_fiber.mp hw)).isPrime,
      fiberCenter_liesOver (Place.mem_fiber.mp hw)⟩) ?_ ?_ ?_ ?_
  · intro w hw; exact Finset.mem_univ _
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq (Place.mem_fiber.mp hw) (Place.mem_fiber.mp hw')
      (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · intro P hP
    have hPne : P.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (maximalIdeal_ne_bot v) P.2
    let Q : HeightOneSpectrum (integralClosureAt F' v) := ⟨P.1, P.2.1, hPne⟩
    refine ⟨placeOfPrime Q, Place.mem_fiber.mpr (restrict_placeOfPrime Q), ?_⟩
    apply Subtype.ext
    exact congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime Q)
  · intro w hw
    let hwv := Place.mem_fiber.mp hw
    let Q := fiberCenter F' v hwv
    let : Q.asIdeal.IsPrime := Q.isPrime
    let : Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
      fiberCenter_liesOver hwv
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter hwv,
      inertiaDeg_eq_inertiaDeg_fiberCenter hwv,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot v)]

end Assembly

end Place

scoped instance instSumRamificationInertia {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] :
    SumRamificationInertia K F F' :=
  ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg_infra v⟩

end AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [HasPrincipalDivisors K F'] (v : Place K F) : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) *
  (w.inertiaDeg F : ℤ) = (Module.finrank F F' : ℤ) :=
  AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_infra v

end
end
end
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg
end ProofImplementation
