/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.NormedValued
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity

/-!
# Continuity of the all-place idele norm

Local norms are determinants on the actual finite-dimensional completed extensions.
On the open product of local integral-unit groups, their finite products give a
continuous map into the target integral-unit product. Translation then supplies
continuity on the whole restricted product.
-/

open scoped AlgebraicCurve.Place Valued WithZero

noncomputable section

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The field norm on the actual completed extension is continuous on units. -/
theorem continuous_localNorm (w : AlgebraicCurve.Place k L) :
    Continuous (localNorm (K := K) w) := by
  have : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    (w.restrict K).kw_ffgc_rankOne_adicCompletion
  have : (Valued.v : Valuation w.adicCompletion ℤᵐ⁰).RankOne :=
    w.kw_ffgc_rankOne_adicCompletion
  let : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  exact LocalFieldTheory.normUnits_continuous_of_finiteDimensional
    (w.restrict K).adicCompletion w.adicCompletion

/-- Identifying the restricted place preserves continuity of its local norm. -/
theorem continuous_localNormOver (v : AlgebraicCurve.Place k K)
    (w : AlgebraicCurve.Place k L) (hw : w.restrict K = v) :
    Continuous (localNormOver v w hw) := by
  subst v
  exact continuous_localNorm w

/-- Each component of the idele norm is a continuous finite product of local norms. -/
theorem continuous_normComponent (v : AlgebraicCurve.Place k K) :
    Continuous (normComponent (k := k) (K := K) (L := L) v) := by
  classical
  change Continuous (fun a : IdeleGroup k L => ∏ w : v.fiberOver L,
    localNormOver v w.1 ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2) (a w.1))
  apply continuous_finsetProd Finset.univ
  intro w _
  exact (continuous_localNormOver v w.1
    ((AlgebraicCurve.Place.mem_fiberOver v).mp w.2)).comp
    (RestrictedProduct.continuous_eval w.1)

/-- The norm is continuous for the all-place restricted-product topologies. -/
theorem continuous_norm : Continuous (norm (k := k) (K := K) (L := L)) := by
  let srcChart : (∀ w : AlgebraicCurve.Place k L, w.adicCompletionIntegers.units) →
      IdeleGroup k L :=
    RestrictedProduct.structureMap _ _ Filter.cofinite
  let tgtChart : (∀ v : AlgebraicCurve.Place k K, v.adicCompletionIntegers.units) →
      IdeleGroup k K :=
    RestrictedProduct.structureMap _ _ Filter.cofinite
  have hsrc : Topology.IsOpenEmbedding srcChart :=
    RestrictedProduct.isOpenEmbedding_structureMap (isOpen_localUnits (k := k) (K := L))
  have htgt : Continuous tgtChart := RestrictedProduct.isEmbedding_structureMap.continuous
  let phi : (∀ w : AlgebraicCurve.Place k L, w.adicCompletionIntegers.units) →
      ∀ v : AlgebraicCurve.Place k K, v.adicCompletionIntegers.units :=
    fun a v => ⟨normComponent (k := k) (K := K) (L := L) v (srcChart a),
      normComponent_mem_localUnits v (srcChart a) (fun w _ => (a w).2)⟩
  have hphi : Continuous phi := by
    apply continuous_pi
    intro v
    exact ((continuous_normComponent (k := k) (K := K) (L := L) v).comp
      hsrc.continuous).subtype_mk _
  have heq : (norm (k := k) (K := K) (L := L)) ∘ srcChart = tgtChart ∘ phi := by
    funext a
    apply RestrictedProduct.ext
    intro v
    rfl
  have hchart : Continuous ((norm (k := k) (K := K) (L := L)) ∘ srcChart) := by
    rw [heq]
    exact htgt.comp hphi
  have h1 : srcChart (1 : ∀ w : AlgebraicCurve.Place k L, w.adicCompletionIntegers.units) =
      (1 : IdeleGroup k L) := by
    apply RestrictedProduct.ext
    intro w
    rfl
  apply continuous_of_continuousAt_one (norm (k := k) (K := K) (L := L))
  have hAt : ContinuousAt (norm (k := k) (K := K) (L := L))
      (srcChart (1 : ∀ w : AlgebraicCurve.Place k L, w.adicCompletionIntegers.units)) :=
    (hsrc.continuousAt_iff
      (g := (norm (k := k) (K := K) (L := L) : IdeleGroup k L → IdeleGroup k K))).mp
      hchart.continuousAt
  rw [h1] at hAt
  exact hAt

/-- The all-place norm as a continuous group homomorphism. -/
def normContinuous : IdeleGroup k L →ₜ* IdeleGroup k K where
  __ := norm (k := k) (K := K) (L := L)
  continuous_toFun := continuous_norm

@[simp]
theorem normContinuous_apply (a : IdeleGroup k L) :
    normContinuous (K := K) (L := L) a = norm (K := K) (L := L) a :=
  rfl

end FunctionField.IdeleGroup

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The descended norm is continuous for the existing quotient topology. -/
theorem continuous_norm : Continuous (norm (k := k) (K := K) (L := L)) := by
  apply continuous_coinduced_dom.2
  exact QuotientGroup.continuous_mk.comp
    (IdeleGroup.continuous_norm (k := k) (K := K) (L := L))

/-- The norm on idele classes as a continuous group homomorphism. -/
def normContinuous : IdeleClassGroup k L →ₜ* IdeleClassGroup k K where
  __ := norm (k := k) (K := K) (L := L)
  continuous_toFun := continuous_norm

@[simp]
theorem normContinuous_apply (c : IdeleClassGroup k L) :
    normContinuous (K := K) (L := L) c = norm (K := K) (L := L) c :=
  rfl

end FunctionField.IdeleClassGroup
