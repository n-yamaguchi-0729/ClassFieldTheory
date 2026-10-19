/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Finite
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.PurelyInseparableDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ValuedFieldTheory.Valuation.Completion.BaseChangeNormTrace
import Nyll.ValuedFieldTheory.Valuation.Completion.DenseTensorProduct

/-!
# Principal norms for purely inseparable extensions

The actual tensor map onto a completed extension is bijective because completion
preserves the purely inseparable degree. The general scalar-extension formula
for algebra norms therefore gives the principal local norm formula.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place TensorProduct WithZero

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsPurelyInseparable K L]

/-- The original field norm equals the completed norm in a finite purely
inseparable extension of function fields. -/
theorem completionNorm_of_isPurelyInseparable (w : Place k L) (x : L) :
    algebraMap K (w.restrict K).adicCompletion (Algebra.norm K x) =
      Algebra.norm (w.restrict K).adicCompletion (algebraMap L w.adicCompletion x) := by
  have hbase : IsScalarTower K (w.restrict K).adicCompletion w.adicCompletion :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply K L w.adicCompletion]
      exact Place.adicCompletionComap_algebraMap_algebraMap K w a
  let hRankOne : (Valued.v : Valuation (w.restrict K).adicCompletion ℤᵐ⁰).RankOne :=
    Place.kw_ffgc_rankOne_adicCompletion (w.restrict K)
  let hNormed : NontriviallyNormedField (w.restrict K).adicCompletion :=
    Valued.toNontriviallyNormedField (w.restrict K).adicCompletion ℤᵐ⁰
  let g : L →ₐ[K] w.adicCompletion := IsScalarTower.toAlgHom K L w.adicCompletion
  let f : (w.restrict K).adicCompletion ⊗[K] L →ₐ[(w.restrict K).adicCompletion]
      w.adicCompletion :=
    Algebra.TensorProduct.lift (Algebra.ofId (w.restrict K).adicCompletion w.adicCompletion)
      g (fun _ _ => Commute.all _ _)
  have hdense : DenseRange g :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w.heightOneSpectrum
  have hsurj : Function.Surjective f :=
    ValuationTheory.Completion.tensorProduct_lift_surjective_of_denseRange
      (A := (w.restrict K).adicCompletion) g hdense
  have hdim : Module.finrank (w.restrict K).adicCompletion
      ((w.restrict K).adicCompletion ⊗[K] L) =
        Module.finrank (w.restrict K).adicCompletion w.adicCompletion := by
    rw [Module.finrank_baseChange, finrank_adicCompletion_eq_of_isPurelyInseparable w]
  let e : (w.restrict K).adicCompletion ⊗[K] L ≃ₐ[(w.restrict K).adicCompletion]
      w.adicCompletion :=
    AlgEquiv.ofBijective f
      (OrzechProperty.bijective_of_surjective_of_finrank_le f.toLinearMap hsurj hdim.le)
  have he : e (1 ⊗ₜ[K] x) = algebraMap L w.adicCompletion x := by
    change f (1 ⊗ₜ[K] x) = g x
    exact (Algebra.TensorProduct.lift_tmul
      (Algebra.ofId (w.restrict K).adicCompletion w.adicCompletion)
      g (fun _ _ => Commute.all _ _) 1 x).trans (by rw [map_one, one_mul])
  calc
    algebraMap K (w.restrict K).adicCompletion (Algebra.norm K x) =
        Algebra.norm (w.restrict K).adicCompletion
          (1 ⊗ₜ[K] x : (w.restrict K).adicCompletion ⊗[K] L) :=
      (ValuationTheory.Completion.algebra_norm_baseChange_tmul
        (A := (w.restrict K).adicCompletion) x).symm
    _ = Algebra.norm (w.restrict K).adicCompletion (e (1 ⊗ₜ[K] x)) :=
      (Algebra.norm_eq_of_algEquiv e (1 ⊗ₜ[K] x)).symm
    _ = Algebra.norm (w.restrict K).adicCompletion
        (algebraMap L w.adicCompletion x) := congrArg _ he

/-- On embedded global units, the actual completed unit norm is the embedded
global unit norm, also for purely inseparable finite extensions. -/
theorem localNorm_principal_of_isPurelyInseparable (w : Place k L) (x : Lˣ) :
    IdeleGroup.localNorm (K := K) w
        (Units.map (algebraMap L w.adicCompletion) x) =
      Units.map (algebraMap K (w.restrict K).adicCompletion)
        (Units.map (Algebra.norm K) x) := by
  apply Units.ext
  exact (completionNorm_of_isPurelyInseparable w (x : L)).symm

end FunctionField
