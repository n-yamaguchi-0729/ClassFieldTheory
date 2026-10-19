/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Ramification.FiniteRamification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormCompact
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormPreimage

/-!
# Open actual norm images and finite norm quotients

At the finitely many ramified base places, impose the open local norm condition.
At every other place, integral units are norms of integral units. These actual
local preimages assemble into an idele. Consequently the idele norm range
contains an open identity neighborhood, and its image in the class group is
open. The already proved compact norm quotient is therefore finite.

The local norm-openness theorem currently has universe `Type`, so these
endpoints retain that restriction explicitly.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

namespace IdeleGroup

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- The local norm subgroup remains open after identifying the restricted place with its base. -/
theorem isOpen_localNormOver_range (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) :
    IsOpen ((localNormOver v w hw).range : Set v.adicCompletionˣ) := by
  subst v
  exact isOpen_localNorm_range (K := K) w

/-- Unramified local integral norm preimages transport along equality of the base place. -/
theorem exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (he : w.ramificationIndex K = 1) (x : v.adicCompletionˣ)
    (hx : x ∈ v.adicCompletionIntegers.units) :
    ∃ y : w.adicCompletionˣ, y ∈ w.adicCompletionIntegers.units ∧
      localNormOver v w hw y = x := by
  subst v
  exact exists_integral_localNorm_eq_of_ramificationIndex_eq_one (K := K) w he x hx

/-- Actual norms on all-place ideles form an open subgroup for a finite Galois extension. -/
theorem isOpen_norm_range :
    IsOpen ((norm (k := k) (K := K) (L := L)).range : Set (IdeleGroup k K)) := by
  classical
  choose w hw using (fun v : Place k K => Place.exists_restrict_eq (M := L) v)
  obtain ⟨S, hS⟩ :=
    exists_finset_forall_restrict_not_mem_ramificationIndex_eq_one_of_isSeparable
      (K := k) (F := K) (F' := L)
  let U : Set (IdeleGroup k K) :=
    (integralSubgroup (k := k) (K := K) : Set (IdeleGroup k K)) ∩
      ⋂ v ∈ S, (fun a : IdeleGroup k K => a v) ⁻¹'
        ((localNormOver v (w v) (hw v)).range : Set v.adicCompletionˣ)
  have hU : IsOpen U :=
    isOpen_integralSubgroup.inter (isOpen_biInter_finset fun v _ =>
      (isOpen_localNormOver_range v (w v) (hw v)).preimage
        (RestrictedProduct.continuous_eval v))
  have hone : (1 : IdeleGroup k K) ∈ U := by
    refine ⟨(integralSubgroup (k := k) (K := K)).one_mem, ?_⟩
    exact Set.mem_iInter.mpr fun v => Set.mem_iInter.mpr fun _ =>
      (localNormOver v (w v) (hw v)).range.one_mem
  have hsub : U ⊆ (norm (k := k) (K := K) (L := L)).range := by
    intro a ha
    have hex (v : Place k K) :
        ∃ b : IdeleGroup k L,
          normComponent (k := k) (K := K) (L := L) v b = a v ∧
          (v ∉ S → fiberProjection (L := L) v b ∈ fiberIntegralUnits (L := L) v) := by
      by_cases hv : v ∈ S
      · have haN : a v ∈ (localNormOver v (w v) (hw v)).range :=
          Set.mem_iInter.mp (Set.mem_iInter.mp ha.2 v) hv
        obtain ⟨x, hx⟩ := haN
        refine ⟨placeIdele (w v) x, (normComponent_placeIdele v (w v) (hw v) x).trans hx,
          fun hn => (hn hv).elim⟩
      · have he : (w v).ramificationIndex K = 1 :=
          hS (w v) (by simpa only [hw v] using hv)
        obtain ⟨x, hxint, hx⟩ :=
          exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
            v (w v) (hw v) he (a v) (ha.1 v)
        refine ⟨placeIdele (w v) x,
          (normComponent_placeIdele v (w v) (hw v) x).trans hx, ?_⟩
        exact fun _ => fiberProjection_placeIdele_mem_integral v (w v) x hxint
    choose b hb hbi using hex
    apply mem_norm_range_of_normComponent_preimages a b hb
    have haway : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ S :=
      S.finite_toSet.compl_mem_cofinite
    exact haway.mono fun v hv => hbi v hv
  exact (norm (k := k) (K := K) (L := L)).range.isOpen_of_mem_nhds
    (Filter.mem_of_superset (hU.mem_nhds hone) hsub)

end IdeleGroup

namespace IdeleClassGroup

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- The actual class norm range is the image of the actual idele norm range. -/
theorem norm_range_eq_image_mk :
    ((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) =
      mk (k := k) (K := K) ''
        ((IdeleGroup.norm (k := k) (K := K) (L := L)).range : Set (IdeleGroup k K)) := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) b
    exact ⟨IdeleGroup.norm (k := k) (K := K) (L := L) a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    exact ⟨mk (k := k) (K := L) b, rfl⟩

/-- The actual finite-extension norm subgroup is open in the ordinary idele-class topology. -/
theorem isOpen_norm_range :
    IsOpen ((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) := by
  rw [norm_range_eq_image_mk]
  exact QuotientGroup.isOpenMap_coe _
    (IdeleGroup.isOpen_norm_range (k := k) (K := K) (L := L))

/-- The actual norm quotient carries the discrete quotient topology. -/
theorem normQuotient_discreteTopology :
    DiscreteTopology (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) :=
  QuotientGroup.discreteTopology (isOpen_norm_range (k := k) (K := K) (L := L))

/-- The actual norm quotient is finite, by compactness and openness of the norm image. -/
theorem normQuotient_finite :
    Finite (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) := by
  have : CompactSpace
      (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) :=
    normQuotient_compactSpace
  have : DiscreteTopology
      (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) :=
    normQuotient_discreteTopology
  exact finite_of_compact_of_discrete

/-- The actual norm subgroup has finite index, without assuming its class-field index formula. -/
theorem norm_range_finiteIndex : (norm (k := k) (K := K) (L := L)).range.FiniteIndex := by
  have : Finite (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) :=
    normQuotient_finite
  exact Subgroup.finiteIndex_of_finite_quotient

end IdeleClassGroup

end FunctionField
