/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendentalPerfectField
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental
public import Nyll.AlgebraicCurves.Places.Orders.BasicTranscendental
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Function fields and the all-place curve API

A finite extension of a rational function field over a perfect field satisfies the existing
`AlgebraicCurve.IsCurveOver` condition. The chosen rational parameter need not be separating:
the curve theorem constructs a separating parameter from perfectness. Over a finite base field,
every place therefore has a finite residue field, including places above infinity.
-/

@[expose] public section

namespace FunctionField

variable (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- Mathlib's function field over a perfect field has principal divisors, finite-dimensional
residue fields and a one-dimensional module of differentials. -/
theorem isCurveOver [PerfectField k] : AlgebraicCurve.IsCurveOver k K := by
  have htr : Transcendental k (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := K)
      (algebraMap (RatFunc k) K).injective).2 (RatFunc.transcendental_X (K := k))
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr
    (FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K))

/-- The residue field of every place of a function field over a finite field is finite. -/
theorem finite_residueField [Finite k] (v : AlgebraicCurve.Place k K) :
    Finite v.ResidueField := by
  have : AlgebraicCurve.IsCurveOver k K := isCurveOver k K
  have : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  exact Module.finite_of_finite k

/-- A one-variable function field over a perfect field has a place, independently
of whether the chosen rational-function-field presentation is separable. -/
theorem nonempty_place [PerfectField k] :
    Nonempty (AlgebraicCurve.Place k K) := by
  have htr : Transcendental k (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := K)
      (algebraMap (RatFunc k) K).injective).2 (RatFunc.transcendental_X (K := k))
  obtain ⟨t, ht, htfin, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr
      (FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K))
  have : Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set K)) K := htsep
  exact AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional k t ht htfin

end FunctionField

namespace ClassFieldTheory.FunctionField

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]

/-- An essentially finite type field of transcendence degree one has a finite
rational-function-field presentation over its original base field. -/
theorem exists_ratFuncAlgebra_of_trdeg_eq_one (htrdeg : Algebra.trdeg k K = 1) :
    ∃ a : Algebra (RatFunc k) K,
      let _ : Algebra (RatFunc k) K := a
      IsScalarTower k (RatFunc k) K ∧ _root_.FunctionField k K := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  have hcard : Cardinal.mk s = 1 := hs.cardinalMk_eq_trdeg.trans htrdeg
  have hsone : s.ncard = 1 := by
    rw [← Nat.card_coe_set_eq, Nat.card, hcard, map_one]
  obtain ⟨t, rfl⟩ := Set.ncard_eq_one.mp hsone
  have htr : Transcendental k t := by
    have hcoe : (Subtype.val : ({t} : Set K) → K) = fun _ => t :=
      funext fun x => Set.mem_singleton_iff.mp x.property
    have hind := hs.1
    rw [hcoe] at hind
    exact (algebraicIndependent_unique_type_iff (ι := ({t} : Set K))).mp hind
  let E := k⟮t⟯
  have hAlg : Algebra.IsAlgebraic E K := by
    have h := hs.isAlgebraic_field
    rwa [Subtype.range_coe] at h
  have : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp k E K
  have : Module.Finite E K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let e : RatFunc k ≃ₐ[k] E := RatFunc.algEquivOfTranscendental t htr
  let a : Algebra (RatFunc k) K := ((algebraMap E K).comp e.toAlgHom.toRingHom).toAlgebra
  refine ⟨a, ?_⟩
  intro sharedAlgebra
  let : Algebra (RatFunc k) E := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (RatFunc k) E :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) E) e.surjective
  refine ⟨IsScalarTower.of_algebraMap_eq fun x => ?_, Module.Finite.trans E K⟩
  change algebraMap k K x = algebraMap E K (e (algebraMap k (RatFunc k) x))
  rw [e.commutes, ← IsScalarTower.algebraMap_apply]

end ClassFieldTheory.FunctionField
