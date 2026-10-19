/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormLocalCriterion

/-!
# Locally zero cyclic unit H² classes and principal idele norms

The completed cohomology criterion is equivalent to actual local norm equations.
Integral local solutions then assemble into an actual idele norm.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open ClassFieldTower.Cohomology

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- A base-unit H² class is zero at every completion exactly when its principal
idele is an actual idele norm. -/
theorem baseUnitH2Class_locally_zero_iff_principal_norm
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    (∀ w : Place k L,
      completionUnitsH2Map (K := K) w (finiteCyclicBaseUnitH2Class K L g hg a) = 0) ↔
      principalIdele k K a ∈ (norm (k := k) (K := K) (L := L)).range := by
  constructor
  · intro hzero
    apply (mem_norm_range_iff_forall_localNorm (K := K) (L := L) (principalIdele k K a)).mpr
    intro w
    obtain ⟨x, hx⟩ := (completionUnitsH2Map_baseUnitClass_eq_zero_iff_norm w g hg a).mp (hzero w)
    have hx0 : x ≠ 0 := by
      intro hz
      have hunit := (Units.map (algebraMap K (w.restrict K).adicCompletion).toMonoidHom a).ne_zero
      apply hunit
      change algebraMap K (w.restrict K).adicCompletion (a : K) = 0
      rw [← hx, hz, Algebra.norm_zero]
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  · rintro ⟨b, hb⟩ w
    exact completionUnitsH2Map_baseUnitClass_eq_zero_of_principal_norm g hg a b hb w

end FunctionField.IdeleGroup
