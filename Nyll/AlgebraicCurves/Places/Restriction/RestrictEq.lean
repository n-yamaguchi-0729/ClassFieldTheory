/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.ValuedFieldTheory.Valuation.Subring.Discrete.DVRAlgebraMapMemFinite
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension

/-!
# Place exists restrict eq

Places extend through algebraic field extensions with the prescribed restriction.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_restrict_eq

noncomputable section
open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place
  _root_.AlgebraicCurves.Places.Proofs.Place_exists_restrict_eq.AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.exists_restrict_eq {K F' M : Type*} [Field K] [Field F']
  [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by
  obtain ⟨O, _, _, hO⟩ :=
    ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
      (L := M) w.toValuationSubring.valuation
  have hpull (x : F') : algebraMap F' M x ∈ O ↔ x ∈ w.toValuationSubring := by
    simpa only [ValuationSubring.valuationSubring_valuation, ValuationSubring.mem_toSubring]
      using hO x
  have hproper : O ≠ ⊤ := by
    intro htop
    apply w.ne_top'
    apply top_unique
    intro x _
    apply (hpull x).mp
    rw [htop]
    exact ValuationSubring.mem_top _
  let aOM : Algebra w.toValuationSubring M :=
    ((algebraMap F' M).comp w.toValuationSubring.subtype).toAlgebra
  have hOM : IsScalarTower w.toValuationSubring F' M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hDVR : IsDiscreteValuationRing O :=
    ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
      (A := w.toValuationSubring) (K := F') O
      (fun a => (hpull a).mpr a.property) hproper
  let W : Place K M :=
    { toValuationSubring := O
      algebraMap_mem' := fun c => by
        rw [IsScalarTower.algebraMap_apply K F' M]
        exact (hpull (algebraMap K F' c)).mpr (w.algebraMap_mem' c)
      ne_top' := hproper
      isPrincipalIdealRing' := inferInstance }
  refine ⟨W, Place.ext ?_⟩
  apply ValuationSubring.ext
  exact hpull

end
end AlgebraicCurves.Places.Proofs.Place_exists_restrict_eq
end ProofImplementation
