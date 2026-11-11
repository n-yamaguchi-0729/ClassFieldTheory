/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_pos.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqInertiaDegFiberCenter
public import Mathlib.NumberTheory.RamificationInertia.Inertia

/-!
# Place inertia Deg pos
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_inertiaDeg_pos

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

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

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.inertiaDeg_pos {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] (w : Place K F') : 0 < w.inertiaDeg F := by
  have := Place.fiberCenter_liesOver (F' := F') (v := w.restrict F) rfl
  rw [Place.inertiaDeg_eq_inertiaDeg_fiberCenter (w.restrict F) rfl]
  exact Ideal.inertiaDeg_pos _ _
end AlgebraicCurves.Places.Proofs.Place_inertiaDeg_pos
end ProofImplementation
