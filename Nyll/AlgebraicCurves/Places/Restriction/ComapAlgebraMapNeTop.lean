/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_comap_algebraMap_ne_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place comap algebra Map ne top
-/

@[expose] public section

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F'] [Algebra F F'] (w : Place K F') [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'
  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  let : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  let : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2
