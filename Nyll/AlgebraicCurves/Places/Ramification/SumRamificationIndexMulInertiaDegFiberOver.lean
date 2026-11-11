/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Nyll.AlgebraicCurves.Places.Basic
public import Mathlib.Util.WithWeakNamespace

/-!
# Place sum ramificationIndex mul inertiaDeg fiberOver

The ramification-index and inertia-degree sum is expressed over the finite fibre of places above a
base place.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver

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

private theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw

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

section Assembly

variable (v : Place K F)

theorem sum_ramificationIndex_mul_inertiaDeg_fiberOver :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v)
  rw [← IsFractionRing.finrank_eq v.toValuationSubring F (integralClosureAt F' v) F'] at hkey
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => ⟨(fiberCenter F' v ((mem_fiberOver v).mp hw)).asIdeal,
      (fiberCenter F' v ((mem_fiberOver v).mp hw)).isPrime,
      fiberCenter_liesOver ((mem_fiberOver v).mp hw)⟩) ?_ ?_ ?_ ?_
  · intro w hw; exact Finset.mem_univ _
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((mem_fiberOver v).mp hw) ((mem_fiberOver v).mp hw')
      (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · intro P hP
    have hPne : P.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (maximalIdeal_ne_bot v) P.2
    let Q : HeightOneSpectrum (integralClosureAt F' v) := ⟨P.1, P.2.1, hPne⟩
    refine ⟨placeOfPrime Q, (mem_fiberOver v).mpr (restrict_placeOfPrime Q), ?_⟩
    apply Subtype.ext
    exact congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime Q)
  · intro w hw
    let hwv := (mem_fiberOver v).mp hw
    let Q := fiberCenter F' v hwv
    let : Q.asIdeal.IsPrime := Q.isPrime
    let : Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
      fiberCenter_liesOver hwv
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter hwv,
      inertiaDeg_eq_inertiaDeg_fiberCenter hwv,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot v)]

end Assembly

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve

with_weak_namespace AlgebraicCurve
theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ) :=
  Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver v
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
end ProofImplementation
