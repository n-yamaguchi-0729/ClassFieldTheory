/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteRingEquiv
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.DenseEmbedding

/-!
# Semilinear automorphisms on completed function fields

The existing action on places preserves the normalized valuation. Completing
the resulting valued field isomorphism gives an isomorphism between the actual
adic completions used in the adele and idele groups. This construction uses the
generic completion isomorphism and preserves the integral subrings and units.

The base field may also be acted on: no choice of full constant field or
separating parameter is needed.
-/

open scoped WithZero

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

open AlgebraicCurve

/-- The place action preserves the normalized multiplicative valuation. -/
theorem place_adicValuation_smul (g : SemilinearAut k K) (v : Place k K) (x : K) :
    (g • v).adicValuation (g • x) = v.adicValuation x := by
  rcases eq_or_ne x 0 with rfl | hx
  · change (g • v).adicValuation (SemilinearAut.toRingAut g 0) = v.adicValuation 0
    simp only [map_zero]
  · have hgx : g • x ≠ 0 := by
      change SemilinearAut.toRingAut g x ≠ 0
      exact (map_ne_zero_iff _ (SemilinearAut.toRingAut g).injective).mpr hx
    have hlog : WithZero.log ((g • v).adicValuation (g • x)) =
        WithZero.log (v.adicValuation x) :=
      neg_injective (SemilinearAut.ord_smul g v x)
    calc
      (g • v).adicValuation (g • x) =
          WithZero.exp (WithZero.log ((g • v).adicValuation (g • x))) :=
        (WithZero.exp_log ((g • v).adicValuation_ne_zero hgx)).symm
      _ = WithZero.exp (WithZero.log (v.adicValuation x)) := congrArg WithZero.exp hlog
      _ = v.adicValuation x := WithZero.exp_log (v.adicValuation_ne_zero hx)

private def placeDiscreteValuation (v : Place k K) :
    ValuationTheory.DiscreteValuationField.DVF K where
  ValueGroup := ℤᵐ⁰
  valuation := v.adicValuation

private theorem placeValuation_isEquiv (g : SemilinearAut k K) (v : Place k K) :
    v.adicValuation.IsEquiv
      ((g • v).adicValuation.comap (SemilinearAut.toRingAut g).toRingHom) := by
  intro x y
  change v.adicValuation x ≤ v.adicValuation y ↔
    (g • v).adicValuation (g • x) ≤ (g • v).adicValuation (g • y)
  rw [place_adicValuation_smul, place_adicValuation_smul]

/-- A semilinear automorphism induces an isomorphism of the corresponding completions. -/
def placeCompletionRingEquiv (g : SemilinearAut k K) (v : Place k K) :
    v.adicCompletion ≃+* (g • v).adicCompletion :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K v.heightOneSpectrum).trans
    ((ValuationTheory.DiscreteValuationField.DVF.completionRingEquiv
      (placeDiscreteValuation v) (placeDiscreteValuation (g • v))
      (SemilinearAut.toRingAut g) (placeValuation_isEquiv g v)).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K
        (g • v).heightOneSpectrum).symm)

/-- The completed map restricts to the original semilinear field automorphism. -/
@[simp]
theorem placeCompletionRingEquiv_algebraMap (g : SemilinearAut k K) (v : Place k K)
    (x : K) :
    placeCompletionRingEquiv g v (algebraMap K v.adicCompletion x) =
      algebraMap K (g • v).adicCompletion (g • x) := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change ValuationTheory.DiscreteValuationField.DVF.completionRingEquiv
      (placeDiscreteValuation v) (placeDiscreteValuation (g • v))
      (SemilinearAut.toRingAut g) (placeValuation_isEquiv g v)
      (algebraMap K v.adicValuation.Completion x) =
    algebraMap K (g • v).adicValuation.Completion (g • x)
  exact ValuationTheory.DiscreteValuationField.DVF.completionRingEquiv_algebraMap
    (placeDiscreteValuation v) (placeDiscreteValuation (g • v))
    (SemilinearAut.toRingAut g) (placeValuation_isEquiv g v) x

/-- The inverse completed map also recovers the original field automorphism. -/
@[simp]
theorem placeCompletionRingEquiv_symm_algebraMap
    (g : SemilinearAut k K) (v : Place k K) (x : K) :
    (placeCompletionRingEquiv g v).symm (algebraMap K (g • v).adicCompletion x) =
      algebraMap K v.adicCompletion (g⁻¹ • x) := by
  apply (placeCompletionRingEquiv g v).injective
  rw [RingEquiv.apply_symm_apply, placeCompletionRingEquiv_algebraMap, smul_inv_smul]

/-- Continuity of the actual completed field isomorphism. -/
theorem continuous_placeCompletionRingEquiv (g : SemilinearAut k K) (v : Place k K) :
    Continuous (placeCompletionRingEquiv g v) := by
  change Continuous
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion ∘
      UniformSpace.Completion.map
        (WithVal.congr v.adicValuation (g • v).adicValuation
          (SemilinearAut.toRingAut g)) ∘
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion)
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K
    (g • v).heightOneSpectrum).comp (UniformSpace.Completion.continuous_map.comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K
        v.heightOneSpectrum))

/-- The inverse completed field isomorphism is continuous as well. -/
theorem continuous_placeCompletionRingEquiv_symm (g : SemilinearAut k K) (v : Place k K) :
    Continuous (placeCompletionRingEquiv g v).symm := by
  change Continuous
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion ∘
      UniformSpace.Completion.map
        (WithVal.congr (g • v).adicValuation v.adicValuation
          (SemilinearAut.toRingAut g).symm) ∘
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion)
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K
    v.heightOneSpectrum).comp (UniformSpace.Completion.continuous_map.comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K
        (g • v).heightOneSpectrum))

open WithZeroTopology in
/-- Preservation of the normalized valuation extends from the dense original field. -/
theorem valued_placeCompletionRingEquiv (g : SemilinearAut k K) (v : Place k K)
    (x : v.adicCompletion) :
    Valued.v (placeCompletionRingEquiv g v x) = Valued.v x := by
  have heq : (fun y : v.adicCompletion =>
      (Valued.v : Valuation (g • v).adicCompletion ℤᵐ⁰)
        (placeCompletionRingEquiv g v y)) =
      (Valued.v : Valuation v.adicCompletion ℤᵐ⁰) := by
    apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      (K := K) (v := v.heightOneSpectrum)).equalizer
    · exact (Valued.continuous_valuation_of_surjective
        ((g • v).heightOneSpectrum.valuedAdicCompletion_surjective K)).comp
        (continuous_placeCompletionRingEquiv g v)
    · exact Valued.continuous_valuation_of_surjective
        (v.heightOneSpectrum.valuedAdicCompletion_surjective K)
    · funext y
      change Valued.v (placeCompletionRingEquiv g v
          (algebraMap K v.adicCompletion y)) =
        Valued.v (algebraMap K v.adicCompletion y)
      rw [placeCompletionRingEquiv_algebraMap]
      calc
        Valued.v (algebraMap K (g • v).adicCompletion (g • y)) =
            (g • v).adicValuation (g • y) :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
            (K := K) (g • v).heightOneSpectrum (g • y)
        _ = v.adicValuation y := place_adicValuation_smul g v y
        _ = Valued.v (algebraMap K v.adicCompletion y) :=
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
            (K := K) v.heightOneSpectrum y).symm
  exact congrFun heq x

/-- The completed isomorphism identifies the integral valuation subrings. -/
theorem placeCompletionRingEquiv_mem_integers_iff
    (g : SemilinearAut k K) (v : Place k K) (x : v.adicCompletion) :
    placeCompletionRingEquiv g v x ∈ (g • v).adicCompletionIntegers ↔
      x ∈ v.adicCompletionIntegers := by
  change Valued.v (placeCompletionRingEquiv g v x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [valued_placeCompletionRingEquiv]

/-- An automorphism fixing the base field induces an isomorphism of completed algebras. -/
def placeCompletionAlgEquiv (σ : K ≃ₐ[k] K) (v : Place k K) :
    v.adicCompletion ≃ₐ[k] (SemilinearAut.ofAlgAut σ • v).adicCompletion where
  __ := placeCompletionRingEquiv (SemilinearAut.ofAlgAut σ) v
  commutes' a := by
    change placeCompletionRingEquiv (SemilinearAut.ofAlgAut σ) v
        (algebraMap k v.adicCompletion a) =
      algebraMap k (SemilinearAut.ofAlgAut σ • v).adicCompletion a
    rw [IsScalarTower.algebraMap_apply k K v.adicCompletion,
      placeCompletionRingEquiv_algebraMap, SemilinearAut.ofAlgAut_smul, σ.commutes,
      ← IsScalarTower.algebraMap_apply k K (SemilinearAut.ofAlgAut σ • v).adicCompletion]

/-- The induced topological isomorphism of the local multiplicative groups. -/
def placeCompletionUnitsEquiv (g : SemilinearAut k K) (v : Place k K) :
    v.adicCompletionˣ ≃ₜ* (g • v).adicCompletionˣ :=
  Units.mapContinuousMulEquiv
    { __ := (placeCompletionRingEquiv g v).toMulEquiv
      continuous_toFun := continuous_placeCompletionRingEquiv g v
      continuous_invFun := continuous_placeCompletionRingEquiv_symm g v }

@[simp]
theorem placeCompletionUnitsEquiv_coe (g : SemilinearAut k K) (v : Place k K)
    (x : v.adicCompletionˣ) :
    (placeCompletionUnitsEquiv g v x : (g • v).adicCompletion) =
      placeCompletionRingEquiv g v (x : v.adicCompletion) :=
  rfl

/-- Integral local units are preserved in both directions. -/
theorem placeCompletionUnitsEquiv_mem_localUnits_iff
    (g : SemilinearAut k K) (v : Place k K) (x : v.adicCompletionˣ) :
    placeCompletionUnitsEquiv g v x ∈ (g • v).adicCompletionIntegers.units ↔
      x ∈ v.adicCompletionIntegers.units := by
  change (placeCompletionRingEquiv g v (x : v.adicCompletion) ∈
        (g • v).adicCompletionIntegers ∧
      placeCompletionRingEquiv g v ((x⁻¹ : v.adicCompletionˣ) : v.adicCompletion) ∈
        (g • v).adicCompletionIntegers) ↔
    ((x : v.adicCompletion) ∈ v.adicCompletionIntegers ∧
      ((x⁻¹ : v.adicCompletionˣ) : v.adicCompletion) ∈ v.adicCompletionIntegers)
  rw [placeCompletionRingEquiv_mem_integers_iff, placeCompletionRingEquiv_mem_integers_iff]

private theorem continuous_completionCast {v w : Place k K} (h : v = w) :
    Continuous (RingEquiv.cast (R := fun u : Place k K => u.adicCompletion) h) := by
  subst w
  exact continuous_id

private theorem completionCast_algebraMap {v w : Place k K} (h : v = w) (x : K) :
    RingEquiv.cast (R := fun u : Place k K => u.adicCompletion) h
      (algebraMap K v.adicCompletion x) = algebraMap K w.adicCompletion x := by
  subst w
  rfl

private theorem completionCast_apply_section {v w : Place k K} (h : v = w)
    (a : ∀ u : Place k K, u.adicCompletion) :
    RingEquiv.cast (R := fun u : Place k K => u.adicCompletion) h (a v) = a w := by
  subst w
  rfl

/-- Acting by the identity on a family of completed elements fixes each component. -/
theorem placeCompletionRingEquiv_symm_one
    (a : ∀ v : Place k K, v.adicCompletion) (v : Place k K) :
    (placeCompletionRingEquiv (1 : SemilinearAut k K)⁻¹ v).symm
      (a ((1 : SemilinearAut k K)⁻¹ • v)) = a v := by
  have hv : (1 : SemilinearAut k K)⁻¹ • v = v := by rw [inv_one, one_smul]
  let c := RingEquiv.cast (R := fun u : Place k K => u.adicCompletion) hv
  have hc : Continuous c := continuous_completionCast hv
  have heq : ((placeCompletionRingEquiv (1 : SemilinearAut k K)⁻¹ v).symm :
      ((1 : SemilinearAut k K)⁻¹ • v).adicCompletion → v.adicCompletion) = c := by
    apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      (K := K) (v := ((1 : SemilinearAut k K)⁻¹ • v).heightOneSpectrum)).equalizer
    · exact continuous_placeCompletionRingEquiv_symm _ v
    · exact hc
    · funext x
      change (placeCompletionRingEquiv (1 : SemilinearAut k K)⁻¹ v).symm
          (algebraMap K ((1 : SemilinearAut k K)⁻¹ • v).adicCompletion x) =
        c (algebraMap K ((1 : SemilinearAut k K)⁻¹ • v).adicCompletion x)
      rw [placeCompletionRingEquiv_symm_algebraMap, completionCast_algebraMap]
      simp only [inv_one, one_smul]
  rw [heq]
  exact completionCast_apply_section hv a

/-- Composition of completed maps agrees with multiplication of semilinear automorphisms.
The statement on families absorbs the canonical transports between equal place indices. -/
theorem placeCompletionRingEquiv_symm_mul (g h : SemilinearAut k K)
    (a : ∀ v : Place k K, v.adicCompletion) (v : Place k K) :
    (placeCompletionRingEquiv (g * h)⁻¹ v).symm (a ((g * h)⁻¹ • v)) =
      (placeCompletionRingEquiv g⁻¹ v).symm
        ((placeCompletionRingEquiv h⁻¹ (g⁻¹ • v)).symm
          (a (h⁻¹ • (g⁻¹ • v)))) := by
  have hv : (g * h)⁻¹ • v = h⁻¹ • (g⁻¹ • v) := by rw [mul_inv_rev, mul_smul]
  let c := RingEquiv.cast (R := fun u : Place k K => u.adicCompletion) hv
  have hc : Continuous c := continuous_completionCast hv
  have heq : ((placeCompletionRingEquiv (g * h)⁻¹ v).symm :
      ((g * h)⁻¹ • v).adicCompletion → v.adicCompletion) =
      (fun x => (placeCompletionRingEquiv g⁻¹ v).symm
        ((placeCompletionRingEquiv h⁻¹ (g⁻¹ • v)).symm (c x))) := by
    apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      (K := K) (v := ((g * h)⁻¹ • v).heightOneSpectrum)).equalizer
    · exact continuous_placeCompletionRingEquiv_symm _ v
    · exact (continuous_placeCompletionRingEquiv_symm g⁻¹ v).comp
        ((continuous_placeCompletionRingEquiv_symm h⁻¹ (g⁻¹ • v)).comp hc)
    · funext x
      change (placeCompletionRingEquiv (g * h)⁻¹ v).symm
          (algebraMap K ((g * h)⁻¹ • v).adicCompletion x) =
        (placeCompletionRingEquiv g⁻¹ v).symm
          ((placeCompletionRingEquiv h⁻¹ (g⁻¹ • v)).symm
            (c (algebraMap K ((g * h)⁻¹ • v).adicCompletion x)))
      simp only [c, completionCast_algebraMap,
        placeCompletionRingEquiv_symm_algebraMap, inv_inv, mul_smul]
  rw [heq]
  exact congrArg (fun y => (placeCompletionRingEquiv g⁻¹ v).symm
    ((placeCompletionRingEquiv h⁻¹ (g⁻¹ • v)).symm y))
    (completionCast_apply_section hv a)

end FunctionField
