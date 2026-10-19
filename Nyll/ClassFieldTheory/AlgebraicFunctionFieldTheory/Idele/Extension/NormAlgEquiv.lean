/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower

/-!
# Norm images under an actual field isomorphism

A field isomorphism is a degree-one field extension. Its actual norm and base
change compare both norm images by the existing norm tower formula.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k K M]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K]
    [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]

/-- Isomorphic finite extensions have the same actual idele-class norm image. -/
theorem norm_range_eq_of_algEquiv (φ : L ≃ₐ[K] M) :
    have _ : FiniteDimensional K M := φ.toLinearEquiv.finiteDimensional
    have _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable φ
    (norm (k := k) (K := K) (L := L)).range =
      (norm (k := k) (K := K) (L := M)).range := by
  intro hKM hKMsep
  let aLM : Algebra L M := φ.toRingHom.toAlgebra
  have hKLM : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hkLM : IsScalarTower k L M := IsScalarTower.to₁₃₄ k K L M
  let φL : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (R := L) (f := φ.toRingEquiv) (fun _ => rfl)
  have hLMfinite : FiniteDimensional L M := φL.toLinearEquiv.finiteDimensional
  have hLMsep : Algebra.IsSeparable L M := AlgEquiv.Algebra.isSeparable φL
  have hdegree : Module.finrank L M = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr φ.bijective
  apply Subgroup.ext
  intro c
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨baseChange (k := k) (K := L) (L := M) d, ?_⟩
    have htower := norm_trans (k := k) (K := K) (L := L) (M := M)
      (baseChange (k := k) (K := L) (L := M) d)
    rw [norm_baseChange, hdegree, pow_one] at htower
    exact htower.symm
  · rintro ⟨d, rfl⟩
    exact ⟨norm (k := k) (K := L) (L := M) d,
      norm_trans (k := k) (K := K) (L := L) (M := M) d⟩

end FunctionField.IdeleClassGroup
