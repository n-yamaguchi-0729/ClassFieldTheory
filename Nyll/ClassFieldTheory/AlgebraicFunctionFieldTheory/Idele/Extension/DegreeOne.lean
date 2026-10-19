/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology

/-!
# Idele classes under a degree-one field extension

The actual base-change map is an isomorphism when the field degree is one.
Its inverse is the actual norm. This compares a field with its embedded image
without choosing unrelated identifications of completed factors.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Degree-one field inclusions induce bijections on actual idele classes. -/
theorem baseChange_bijective_of_finrank_one (h : Module.finrank K L = 1) :
    Function.Bijective (baseChange (k := k) (K := K) (L := L)) := by
  refine ⟨baseChange_injective, ?_⟩
  intro c
  apply exists_baseChange_of_algAut_fixed c
  intro σ
  have hσ : σ = 1 := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 x
    exact σ.commutes a
  rw [hσ]
  change (1 : AlgebraicCurve.SemilinearAut k L) • c = c
  exact one_smul _ _

/-- The actual idele-class isomorphism induced by a degree-one field inclusion. -/
def baseChangeEquivOfFinrankOne (h : Module.finrank K L = 1) :
    IdeleClassGroup k K ≃* IdeleClassGroup k L :=
  MulEquiv.ofBijective (baseChange (k := k) (K := K) (L := L))
    (baseChange_bijective_of_finrank_one h)

/-- Its inverse is the actual all-place class norm. -/
theorem baseChangeEquivOfFinrankOne_symm (h : Module.finrank K L = 1)
    (c : IdeleClassGroup k L) :
    (baseChangeEquivOfFinrankOne (k := k) h).symm c = norm (k := k) (K := K) (L := L) c := by
  obtain ⟨a, rfl⟩ := (baseChange_bijective_of_finrank_one (k := k) h).2 c
  change (baseChangeEquivOfFinrankOne (k := k) h).symm
      (baseChangeEquivOfFinrankOne (k := k) h a) = _
  rw [MulEquiv.symm_apply_apply, norm_baseChange, h, pow_one]

end FunctionField.IdeleClassGroup
