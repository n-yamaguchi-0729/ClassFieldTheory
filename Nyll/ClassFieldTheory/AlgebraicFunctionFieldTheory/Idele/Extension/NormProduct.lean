/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Approximation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormGalois
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The Galois product formula on all-place ideles

Weak approximation makes the original extension field dense in the finite product
of its actual completions above any base place. On this dense subfield the product
of completed norms is the global field norm, and the latter is the product of all
Galois conjugates. Continuity therefore gives the identity for arbitrary completed
components. Applying it at every place proves the all-place idele formula and its
descent to idele classes.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place Valued WithZero

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

/-- The completed field norm with only its base place transported. -/
def completionNormOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    w.adicCompletion →* v.adicCompletion :=
  hw ▸ Algebra.norm (w.restrict K).adicCompletion

/-- The field-valued and unit-valued completed norms are the same map. -/
theorem coe_localNormOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (x : w.adicCompletionˣ) :
    (localNormOver v w hw x : v.adicCompletion) =
      completionNormOver v w hw (x : w.adicCompletion) := by
  subst v
  rfl

/-- Determinant norms on the actual completed extension fields are continuous. -/
theorem continuous_completionNormOver (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) : Continuous (completionNormOver v w hw) := by
  subst v
  have : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    (w.restrict K).kw_ffgc_rankOne_adicCompletion
  have : (Valued.v : Valuation w.adicCompletion ℤᵐ⁰).RankOne :=
    w.kw_ffgc_rankOne_adicCompletion
  let : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  exact LocalFieldTheory.algebraNorm_continuous_of_finiteDimensional
    (w.restrict K).adicCompletion w.adicCompletion

variable [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

private theorem completionNormOver_prod_diagonal (v : Place k K) (x : L) :
    (∏ u : v.fiberOver L, completionNormOver v u.1
      ((Place.mem_fiberOver v).mp u.2) (algebraMap L u.1.adicCompletion x)) =
      algebraMap K v.adicCompletion (Algebra.norm K x) := by
  classical
  rw [AlgebraicCurve.completionNormProduct_of_isSeparable v x]
  let e : v.fiberOver L ≃ v.fiber L :=
    Finset.equivOfEq (Place.fiber_eq_fiberOver v).symm
  refine Fintype.prod_equiv e _ _ ?_
  rintro ⟨u, hu⟩
  have hv : u.restrict K = v := (Place.mem_fiberOver v).mp hu
  subst v
  rfl

/-- The place supplying a conjugated component lies in the same actual finite fiber. -/
def conjugateFiberPoint (σ : L ≃ₐ[K] L) (w : Place k L) : (w.restrict K).fiberOver L :=
  ⟨(SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w,
    (Place.mem_fiberOver (w.restrict K)).mpr (Place.restrict_ofAlgAut_smul σ.symm w)⟩

variable [IsGalois K L]

/-- The product of local norms, included into any extending completion, is the
product of the actual completed Galois conjugates of arbitrary fiber components. -/
theorem completionNormProduct_eq_prod_algAut (w : Place k L)
    (x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion) :
    completionMapOver (w.restrict K) w rfl
        (∏ u : (w.restrict K).fiberOver L,
          completionNormOver (w.restrict K) u.1
            ((Place.mem_fiberOver (w.restrict K)).mp u.2) (x u)) =
      ∏ σ : L ≃ₐ[K] L,
        (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (x (conjugateFiberPoint σ w)) := by
  classical
  have h : (fun x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion =>
      completionMapOver (w.restrict K) w rfl
        (∏ u : (w.restrict K).fiberOver L,
          completionNormOver (w.restrict K) u.1
            ((Place.mem_fiberOver (w.restrict K)).mp u.2) (x u))) =
      (fun x : (u : (w.restrict K).fiberOver L) → u.1.adicCompletion =>
        ∏ σ : L ≃ₐ[K] L,
          (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
            (x (conjugateFiberPoint σ w))) := by
    apply (denseRange_pi_placeCompletion
      (fun u : (w.restrict K).fiberOver L => u.1) Subtype.val_injective).equalizer
    · apply (continuous_completionMapOver (w.restrict K) w rfl).comp
      apply continuous_finsetProd Finset.univ
      intro u _
      exact (continuous_completionNormOver (w.restrict K) u.1
        ((Place.mem_fiberOver (w.restrict K)).mp u.2)).comp (continuous_apply u)
    · apply continuous_finsetProd Finset.univ
      intro σ _
      exact (continuous_placeCompletionRingEquiv_symm
        (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).comp
        (continuous_apply (conjugateFiberPoint σ w))
    · funext t
      change completionMapOver (w.restrict K) w rfl
          (∏ u : (w.restrict K).fiberOver L,
            completionNormOver (w.restrict K) u.1
              ((Place.mem_fiberOver (w.restrict K)).mp u.2)
              (algebraMap L u.1.adicCompletion t)) = _
      rw [completionNormOver_prod_diagonal, completionMapOver_algebraMap,
        Algebra.norm_eq_prod_automorphisms, map_prod]
      apply Finset.prod_congr rfl
      intro σ _
      change algebraMap L w.adicCompletion (σ t) =
        (placeCompletionRingEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
          (algebraMap L
            ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w).adicCompletion t)
      rw [placeCompletionRingEquiv_symm_algebraMap, inv_inv]
      rfl
  exact congrFun h x

/-- Base change of the all-place idele norm is the product of all actual Galois
conjugates, with the action on both places and completed values. -/
theorem baseChange_norm_eq_prod_algAut (a : IdeleGroup k L) :
    baseChange (k := k) (K := K) (L := L) (norm (k := k) (K := K) (L := L) a) =
      ∏ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a := by
  classical
  apply IdeleGroup.ext
  intro w
  rw [component_baseChange, map_prod]
  apply Units.ext
  change completionMapOver (w.restrict K) w rfl
      ((normComponent (k := k) (K := K) (L := L) (w.restrict K) a) :
        (w.restrict K).adicCompletion) = _
  rw [normComponent_apply, Units.coe_prod, Units.coe_prod]
  simp only [coe_localNormOver]
  exact completionNormProduct_eq_prod_algAut w
    (fun u : (w.restrict K).fiberOver L => (a u.1 : u.1.adicCompletion))

end IdeleGroup

namespace IdeleClassGroup

variable [Algebra.IsSeparable K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual Galois product formula descends through the principal-idele quotient. -/
theorem baseChange_norm_eq_prod_algAut (c : IdeleClassGroup k L) :
    baseChange (k := k) (K := K) (L := L) (norm (k := k) (K := K) (L := L) c) =
      ∏ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := L) c
  change baseChange (k := k) (K := K) (L := L)
      (mk (k := k) (K := K) (IdeleGroup.norm (k := k) (K := K) (L := L) a)) = _
  rw [baseChange_mk, IdeleGroup.baseChange_norm_eq_prod_algAut, map_prod]
  simp only [smul_mk]

end IdeleClassGroup

end FunctionField
