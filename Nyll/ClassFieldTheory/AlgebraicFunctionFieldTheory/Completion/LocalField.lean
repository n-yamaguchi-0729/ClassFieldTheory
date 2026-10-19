/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology

/-!
# Local fields at all places of a global function field

The existing completion at an `AlgebraicCurve.Place` has a discrete valuation and its
residue field agrees with the residue field before completion. Over a finite constant
field, this gives local compactness and the nonarchimedean local-field structure used
by local class field theory. Places above infinity are included.

The valuation relation is passed explicitly from the existing adic valuation; the
completion, its topology and its integral subring are not reconstructed.
-/

open scoped Valued WithZero

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The valuative relation induced by the canonical valuation on a place completion. -/
@[reducible]
def placeCompletionValuativeRel (v : AlgebraicCurve.Place k K) :
    ValuativeRel v.adicCompletion :=
  ValuativeRel.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Finite k]

/-- Completion preserves the finite residue field at every place. -/
theorem placeCompletion_finite_residueField (v : AlgebraicCurve.Place k K) :
    Finite (IsLocalRing.ResidueField v.adicCompletionIntegers) := by
  have : Finite v.ResidueField := finite_residueField k K v
  let e : v.ResidueField ≃+* IsLocalRing.ResidueField v.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      K v.heightOneSpectrum
  exact Finite.of_equiv v.ResidueField e.toEquiv

/-- Every place completion of a function field over a finite field is locally compact. -/
theorem placeCompletion_locallyCompactSpace (v : AlgebraicCurve.Place k K) :
    LocallyCompactSpace v.adicCompletion := by
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).RankOne :=
    v.kw_ffgc_rankOne_adicCompletion
  have : Finite 𝓀[v.adicCompletion] := placeCompletion_finite_residueField v
  have : ProperSpace v.adicCompletion :=
    ((open Valued.integer in
      properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := v.adicCompletion) (Γ₀ := ℤᵐ⁰))).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- The integer ring in every actual place completion is compact. -/
theorem isCompact_localIntegers (v : AlgebraicCurve.Place k K) :
    IsCompact (v.adicCompletionIntegers : Set v.adicCompletion) := by
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).RankOne :=
    v.kw_ffgc_rankOne_adicCompletion
  have : LocallyCompactSpace v.adicCompletion := placeCompletion_locallyCompactSpace v
  have : ProperSpace v.adicCompletion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace v.adicCompletion
  change IsCompact (𝒪[v.adicCompletion] : Set v.adicCompletion)
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance)

/-- The actual completion at any place is a nonarchimedean local field for its
canonical valuative relation. No separability condition on the chosen rational
parameter is required. -/
theorem placeCompletion_isNonarchimedeanLocalField (v : AlgebraicCurve.Place k K) :
    let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    IsNonarchimedeanLocalField v.adicCompletion := by
  intro completionRelation
  have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
  have : ValuativeRel.IsNontrivial v.adicCompletion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)).2 inferInstance
  exact
    { toIsValuativeTopology :=
        LocalFieldTheory.isValuativeTopology_of_valued_ofValuation v.adicCompletion ℤᵐ⁰
      toLocallyCompactSpace := placeCompletion_locallyCompactSpace v
      toIsNontrivial := inferInstance }

end FunctionField
