/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

/-! # Existence of a rational point on a curve model over an algebraically closed field -/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicCurve.CurveModel

/-- A curve model has a rational point over an algebraically closed base.
The point is constructed from an actual closed point of its Jacobson space. -/
theorem nonempty_rationalPoint
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) :
    Nonempty (SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) := by
  have : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := M.C) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact ⟨(pointEquivClosedPoint M.toBase).symm ⟨x, hx⟩⟩

end AlgebraicCurve.CurveModel
