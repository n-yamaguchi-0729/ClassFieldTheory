/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place ramification Index eq ramification Idx fiber Center
-/

@[expose] public section

section ProofImplementation


namespace AlgebraicCurves.Places.Proofs.PlaceRamificationIndex

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

private theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0
  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]
  refine (Ideal.ramificationIdx'_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower
  K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.ramificationIndex F = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (Place.fiberCenter F' v hw).asIdeal :=
  PlaceRamificationIndex.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter hw
end AlgebraicCurves.Places.Proofs.PlaceRamificationIndex
end ProofImplementation
