/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormProduct
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisDescent
import Mathlib.RingTheory.Trace.Basic

/-!
# Descent of fixed all-place ideles

The additive Galois trace formula on a finite fiber follows from weak
approximation and continuity. A global element of trace one then gives an actual
preimage in every base completion for a fixed idele. Positive ramification indices
reflect the local integral-unit condition, proving the restricted-product condition
for the descended components.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place Valued WithZero

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The trace on the actual completed field, transported to its specified base place. -/
def completionTraceOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    w.adicCompletion →+ v.adicCompletion :=
  hw ▸ (Algebra.trace (w.restrict K).adicCompletion w.adicCompletion).toAddMonoidHom

/-- Finite-dimensional completed field traces are continuous. -/
theorem continuous_completionTraceOver (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) : Continuous (completionTraceOver v w hw) := by
  subst v
  have : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    (w.restrict K).kw_ffgc_rankOne_adicCompletion
  have : (Valued.v : Valuation w.adicCompletion ℤᵐ⁰).RankOne :=
    w.kw_ffgc_rankOne_adicCompletion
  let : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  exact LinearMap.continuous_of_finiteDimensional
    (Algebra.trace (w.restrict K).adicCompletion w.adicCompletion)

/-- The completed inclusion reflects integral units because its ramification
index is strictly positive. -/
theorem localBaseChange_mem_localUnits_iff (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    localBaseChange (K := K) w x ∈ w.adicCompletionIntegers.units ↔
      x ∈ (w.restrict K).adicCompletionIntegers.units := by
  constructor
  · intro hx
    apply (localOrder_eq_zero_iff _ x).1
    have h := (localOrder_eq_zero_iff w _).2 hx
    change (localOrder w (Units.map
      (algebraMap (w.restrict K).adicCompletion w.adicCompletion) x)).toAdd = 0 at h
    rw [localOrder_completionMap] at h
    exact (mul_eq_zero.mp h).resolve_left
      (Int.natCast_ne_zero.mpr (ne_of_gt w.ramificationIndex_pos))
  · exact localBaseChange_mem_localUnits w x

variable [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

private theorem completionTraceOver_sum_diagonal (v : Place k K) (x : L) :
    (∑ u : v.fiberOver L, completionTraceOver v u.1
      ((Place.mem_fiberOver v).mp u.2) (algebraMap L u.1.adicCompletion x)) =
      algebraMap K v.adicCompletion (Algebra.trace K L x) := by
  classical
  rw [AlgebraicCurve.completionTraceSum_of_isSeparable
    (K := k) (F := L) (E := K) v x, ← Finset.univ_eq_attach]
  let e : v.fiberOver L ≃ v.fiber L :=
    Finset.equivOfEq (Place.fiber_eq_fiberOver v).symm
  apply Fintype.sum_equiv e
  rintro ⟨u, hu⟩
  have h := (Place.mem_fiberOver v).mp hu
  subst v
  rfl

variable [IsGalois K L]

/-- The sum of local traces, included into an extending completion, is the sum
of the actual completed Galois conjugates of arbitrary fiber components. -/
theorem completionTraceSum_eq_sum_algAut (w : Place k L)
    (x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion) :
    completionMapOver (w.restrict K) w rfl
        (∑ u : (w.restrict K).fiberOver L,
          completionTraceOver (w.restrict K) u.1
            ((Place.mem_fiberOver (w.restrict K)).mp u.2) (x u)) =
      ∑ σ : L ≃ₐ[K] L,
        (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (x (conjugateFiberPoint σ w)) := by
  classical
  have h : (fun x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion =>
      completionMapOver (w.restrict K) w rfl
        (∑ u : (w.restrict K).fiberOver L,
          completionTraceOver (w.restrict K) u.1
            ((Place.mem_fiberOver (w.restrict K)).mp u.2) (x u))) =
      (fun x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion =>
        ∑ σ : L ≃ₐ[K] L,
          (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
            (x (conjugateFiberPoint σ w))) := by
    apply (denseRange_pi_placeCompletion
      (fun u : (w.restrict K).fiberOver L => u.1) Subtype.val_injective).equalizer
    · apply (continuous_completionMapOver (w.restrict K) w rfl).comp
      apply continuous_finsetSum Finset.univ
      intro u _
      exact (continuous_completionTraceOver (w.restrict K) u.1
        ((Place.mem_fiberOver (w.restrict K)).mp u.2)).comp (continuous_apply u)
    · apply continuous_finsetSum Finset.univ
      intro σ _
      exact (continuous_placeCompletionRingEquiv_symm
        (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).comp
        (continuous_apply (conjugateFiberPoint σ w))
    · funext t
      change completionMapOver (w.restrict K) w rfl
          (∑ u : (w.restrict K).fiberOver L,
            completionTraceOver (w.restrict K) u.1
              ((Place.mem_fiberOver (w.restrict K)).mp u.2)
              (algebraMap L u.1.adicCompletion t)) = _
      rw [completionTraceOver_sum_diagonal, completionMapOver_algebraMap,
        trace_eq_sum_automorphisms, map_sum]
      apply Finset.sum_congr rfl
      intro σ _
      change algebraMap L w.adicCompletion (σ t) =
        (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (algebraMap L
            ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w).adicCompletion t)
      rw [placeCompletionRingEquiv_symm_algebraMap, inv_inv]
      rfl
  exact congrFun h x

/-- A trace-weighted component in the actual base completion. -/
def descentComponent (a : IdeleGroup k L) (y : L) (v : Place k K) :
    v.adicCompletion :=
  ∑ u : v.fiberOver L, completionTraceOver v u.1
    ((Place.mem_fiberOver v).mp u.2)
    (algebraMap L u.1.adicCompletion y * (a u.1 : u.1.adicCompletion))

/-- A trace-one coefficient reconstructs every component of a fixed idele. -/
theorem completionMap_descentComponent (a : IdeleGroup k L)
    (ha : ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a = a)
    (y : L) (hy : Algebra.trace K L y = 1) (w : Place k L) :
    completionMapOver (w.restrict K) w rfl (descentComponent a y (w.restrict K)) =
      (a w : w.adicCompletion) := by
  classical
  rw [descentComponent, completionTraceSum_eq_sum_algAut]
  calc
    (∑ σ : L ≃ₐ[K] L,
        (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (algebraMap L (conjugateFiberPoint σ w).1.adicCompletion y *
            (a (conjugateFiberPoint σ w).1 : (conjugateFiberPoint σ w).1.adicCompletion))) =
        ∑ σ : L ≃ₐ[K] L, algebraMap L w.adicCompletion (σ y) *
          (a w : w.adicCompletion) := by
      apply Finset.sum_congr rfl
      intro σ _
      change (placeCompletionRingEquiv
        (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (algebraMap L
            ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w).adicCompletion y *
              (a ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w) :
                ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w).adicCompletion)) = _
      rw [map_mul]
      have hσ := congrArg (fun b : IdeleGroup k L => (b w : w.adicCompletion)) (ha σ)
      change (placeCompletionRingEquiv
        (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (a ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w) :
            ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w).adicCompletion) =
          (a w : w.adicCompletion) at hσ
      rw [hσ]
      congr 1
      rw [placeCompletionRingEquiv_symm_algebraMap, inv_inv]
      rfl
    _ = (a w : w.adicCompletion) := by
      rw [← Finset.sum_mul, ← map_sum, ← trace_eq_sum_automorphisms,
        hy, map_one, map_one, one_mul]

/-- Fixed completed components descend to nonzero base components. -/
theorem descentComponent_ne_zero (a : IdeleGroup k L)
    (ha : ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a = a)
    (y : L) (hy : Algebra.trace K L y = 1) (v : Place k K) :
    descentComponent a y v ≠ 0 := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  intro hz
  have h := completionMap_descentComponent a ha y hy w
  rw [hz, map_zero] at h
  exact (a w).ne_zero h.symm

/-- Every fixed all-place idele is the actual inclusion of a base idele.
Trace surjectivity supplies the coefficient, and the finite exceptional set
descends along restriction of places. -/
theorem exists_baseChange_of_algAut_fixed (a : IdeleGroup k L)
    (ha : ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a = a) :
    ∃ b : IdeleGroup k K, baseChange (k := k) (K := K) (L := L) b = a := by
  classical
  obtain ⟨y, hy⟩ := Algebra.trace_surjective K L (1 : K)
  let b (v : Place k K) : v.adicCompletionˣ :=
    Units.mk0 (descentComponent a y v) (descentComponent_ne_zero a ha y hy v)
  have hb (w : Place k L) : localBaseChange (K := K) w (b (w.restrict K)) = a w := by
    apply Units.ext
    exact completionMap_descentComponent a ha y hy w
  have hbad : {w : Place k L | a w ∉ w.adicCompletionIntegers.units}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have haway : ∀ᶠ v : Place k K in Filter.cofinite,
      v ∉ (fun w : Place k L => w.restrict K) ''
        {w : Place k L | a w ∉ w.adicCompletionIntegers.units} :=
    (hbad.image (fun w : Place k L => w.restrict K)).compl_mem_cofinite
  have hbint : ∀ᶠ v : Place k K in Filter.cofinite, b v ∈ v.adicCompletionIntegers.units := by
    apply haway.mono
    intro v hv
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    apply (localBaseChange_mem_localUnits_iff w (b (w.restrict K))).1
    rw [hb]
    by_contra hn
    exact hv ⟨w, hn, rfl⟩
  refine ⟨⟨b, hbint⟩, ?_⟩
  apply IdeleGroup.ext
  intro w
  exact hb w

/-- Membership in the image of the actual base-change map is equivalent to
being fixed by every automorphism of the finite Galois extension. -/
theorem mem_range_baseChange_iff_algAut_fixed (a : IdeleGroup k L) :
    a ∈ (baseChange (k := k) (K := K) (L := L)).range ↔
      ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a = a := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact algAut_smul_baseChange σ b
  · exact exists_baseChange_of_algAut_fixed a

end FunctionField.IdeleGroup

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Fixed idele classes descend through the actual base-change homomorphism:
Hilbert 90 first supplies a fixed representative, and trace-one descent
then descends that representative componentwise. -/
theorem exists_baseChange_of_algAut_fixed (c : IdeleClassGroup k L)
    (hc : ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c) :
    ∃ b : IdeleClassGroup k K, baseChange (k := k) (K := K) (L := L) b = c := by
  classical
  by_cases hplaces : Nonempty (Place k L)
  · have : Nonempty (Place k L) := hplaces
    obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
    obtain ⟨a', hclass, hfixed⟩ := IdeleGroup.exists_fixed_representative_of_fixed_class a hc
    obtain ⟨b, hb⟩ := IdeleGroup.exists_baseChange_of_algAut_fixed a' hfixed
    refine ⟨mk (k := k) (K := K) b, ?_⟩
    rw [baseChange_mk, hb]
    exact hclass
  · obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
    have ha : a = 1 := by
      apply IdeleGroup.ext
      intro w
      exact False.elim (hplaces ⟨w⟩)
    refine ⟨1, ?_⟩
    rw [ha, map_one, map_one]

/-- The fixed idele classes are precisely the image of the base idele classes. -/
theorem mem_range_baseChange_iff_algAut_fixed (c : IdeleClassGroup k L) :
    c ∈ (baseChange (k := k) (K := K) (L := L)).range ↔
      ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact algAut_smul_baseChange σ b
  · exact exists_baseChange_of_algAut_fixed c

end FunctionField.IdeleClassGroup
