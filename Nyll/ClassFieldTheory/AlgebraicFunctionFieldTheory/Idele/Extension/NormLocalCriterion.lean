/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormLocalRange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen

/-!
# Actual idele norms and local norms

Local norm solutions assemble into an idele: away from finitely many ramified
places and nonintegral components, unramified integral norm surjectivity gives
integral solutions. Conjugacy supplies the converse at every upper place.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- An actual idele is a norm exactly when all its completed components are norms. -/
theorem mem_norm_range_iff_forall_localNorm (a : IdeleGroup k K) :
    a ∈ (norm (k := k) (K := K) (L := L)).range ↔
      ∀ w : Place k L, a (w.restrict K) ∈ (localNorm (K := K) w).range := by
  classical
  constructor
  · rintro ⟨b, rfl⟩ w
    exact norm_component_mem_localNorm_range (K := K) w b
  · intro ha
    have hlocal (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
        a v ∈ (localNormOver v w hw).range := by
      subst v
      exact ha w
    choose w hw using (fun v : Place k K => Place.exists_restrict_eq (M := L) v)
    obtain ⟨S, hS⟩ :=
      exists_finset_forall_restrict_not_mem_ramificationIndex_eq_one_of_isSeparable
        (K := k) (F := K) (F' := L)
    let P (v : Place k K) : Prop := v ∉ S ∧ a v ∈ v.adicCompletionIntegers.units
    have hex (v : Place k K) : ∃ b : IdeleGroup k L,
        normComponent (K := K) (L := L) v b = a v ∧
          (P v → fiberProjection (L := L) v b ∈ fiberIntegralUnits (L := L) v) := by
      by_cases hv : P v
      · have he : (w v).ramificationIndex K = 1 :=
          hS (w v) (by simpa only [hw v] using hv.1)
        obtain ⟨x, hxint, hx⟩ :=
          exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
            v (w v) (hw v) he (a v) hv.2
        exact ⟨placeIdele (w v) x,
          (normComponent_placeIdele v (w v) (hw v) x).trans hx,
          fun _ => fiberProjection_placeIdele_mem_integral v (w v) x hxint⟩
      · obtain ⟨x, hx⟩ := hlocal v (w v) (hw v)
        exact ⟨placeIdele (w v) x,
          (normComponent_placeIdele v (w v) (hw v) x).trans hx,
          fun hp => (hv hp).elim⟩
    choose b hb hbi using hex
    apply mem_norm_range_of_normComponent_preimages a b hb
    have haway : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ S :=
      S.finite_toSet.compl_mem_cofinite
    exact (haway.and a.2).mono (fun v hv => hbi v hv)

end FunctionField.IdeleGroup
