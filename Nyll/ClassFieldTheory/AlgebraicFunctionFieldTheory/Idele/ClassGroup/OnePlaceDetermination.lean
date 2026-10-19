/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.DenseEmbedding
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Approximation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.OnePlaceDetermination

/-!
# Idele class characters are determined away from finitely many places

Weak approximation makes principal units dense in any finite product of local
multiplicative groups. A continuous character trivial outside this finite set
therefore vanishes everywhere once it vanishes on principal ideles.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Values at the places outside any finite set determine a continuous idele
class homomorphism into a Hausdorff commutative topological group. -/
theorem continuousMonoidHom_ext_placeIdele_away
    {M : Type*} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [T2Space M]
    (f g : IdeleClassGroup k K →ₜ* M) (S : Finset (AlgebraicCurve.Place k K))
    (h : ∀ (v : AlgebraicCurve.Place k K), v ∉ S → ∀ x : v.adicCompletionˣ,
      f (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
        g (mk (k := k) (K := K) (IdeleGroup.placeIdele v x))) : f = g := by
  classical
  let δ : IdeleGroup k K →ₜ* M :=
    { toMonoidHom := (f.toMonoidHom.comp (mk (k := k) (K := K))) /
        (g.toMonoidHom.comp (mk (k := k) (K := K)))
      continuous_toFun := (f.continuous.comp QuotientGroup.continuous_mk).div'
        (g.continuous.comp QuotientGroup.continuous_mk) }
  have hout (v : AlgebraicCurve.Place k K) (hv : v ∉ S) (x : v.adicCompletionˣ) :
      δ (IdeleGroup.placeIdele v x) = 1 := by
    change f (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) /
      g (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) = 1
    exact div_eq_one.mpr (h v hv x)
  have hprod (a : IdeleGroup k K) :
      δ a = ∏ v ∈ S, δ (IdeleGroup.placeIdele v (a v)) :=
    ((IdeleGroup.hasProd_placeIdele a).map δ.toMonoidHom δ.continuous).unique
      (hasProd_prod_of_ne_finset_one (fun v hv => hout v hv (a v)))
  let ψ : (∀ v : S, v.val.adicCompletionˣ) → M :=
    fun x => ∏ v : S, δ (IdeleGroup.placeIdele v.val (x v))
  have hψ : Continuous ψ :=
    continuous_finsetProd _ (fun v _ => δ.continuous.comp
      ((IdeleGroup.continuous_placeIdele v.val).comp (continuous_apply v)))
  have hprincipal (x : Kˣ) : δ (IdeleGroup.principalIdele k K x) = 1 := by
    have hx : mk (k := k) (K := K) (IdeleGroup.principalIdele k K x) = (1 : IdeleClassGroup k K) :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    change f (mk (k := k) (K := K) (IdeleGroup.principalIdele k K x)) /
      g (mk (k := k) (K := K) (IdeleGroup.principalIdele k K x)) = 1
    rw [hx, map_one, map_one, div_self']
  have hψprincipal :
      ψ ∘ (fun x : Kˣ => fun v : S =>
        Units.map (algebraMap K v.val.adicCompletion).toMonoidHom x) = fun _ => (1 : M) := by
    funext x
    change (∏ v : S, δ (IdeleGroup.placeIdele v.val
      (Units.map (algebraMap K v.val.adicCompletion).toMonoidHom x))) = 1
    exact (Finset.prod_coe_sort S (fun v => δ (IdeleGroup.placeIdele v
      (Units.map (algebraMap K v.adicCompletion).toMonoidHom x)))).trans
        ((hprod (IdeleGroup.principalIdele k K x)).symm.trans (hprincipal x))
  have hψone : ψ = fun _ => (1 : M) :=
    (denseRange_pi_placeCompletionUnits (fun v : S => v.val) Subtype.val_injective).equalizer
      hψ continuous_const hψprincipal
  apply ContinuousMonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ := (show Function.Surjective (mk (k := k) (K := K)) from
    QuotientGroup.mk_surjective) c
  apply div_eq_one.mp
  change δ a = 1
  rw [hprod]
  have hvalue := congrFun hψone (fun v : S => a v.val)
  exact (Finset.prod_coe_sort S
    (fun v => δ (IdeleGroup.placeIdele v (a v)))).symm.trans hvalue

end FunctionField.IdeleClassGroup
