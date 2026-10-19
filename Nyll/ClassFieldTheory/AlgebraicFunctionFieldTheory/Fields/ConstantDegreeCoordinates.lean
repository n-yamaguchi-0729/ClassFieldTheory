/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantClosure
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantFrobenius

/-!
# Finite constant coordinates detect the absolute degree

Equality of profinite degrees is equivalent to equality of restrictions
on all actual finite constant extensions. Integer degrees are therefore
characterized by the corresponding powers of arithmetic Frobenius.
-/

noncomputable section

namespace FunctionField

open ClassFormation

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- Finite constant restrictions detect equality of the actual profinite degree. -/
theorem fullConstantDegreeData_eq_iff_restrict (σ τ : Gal(Ω/K)) :
    (fullConstantDegreeData k K Ω).degree σ = (fullConstantDegreeData k K Ω).degree τ ↔
      ∀ n : ℕ+, AlgEquiv.restrictNormalHom (fullConstantDegreeStage k K Ω n) σ =
        AlgEquiv.restrictNormalHom (fullConstantDegreeStage k K Ω n) τ := by
  let D := fullConstantDegreeData k K Ω
  have hker : D.degree.toMonoidHom.ker =
      ⨅ n : ℕ+, (fullConstantDegreeStage k K Ω n).toIntermediateField.fixingSubgroup :=
    fullConstantDegreeData_inertia_eq_iInf k K Ω
  have hmem := SetLike.ext_iff.mp hker (σ⁻¹ * τ)
  simp only [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    Subgroup.mem_iInf] at hmem
  refine hmem.trans (forall_congr' fun n => ?_)
  rw [← (fullConstantDegreeStage k K Ω n).toIntermediateField.restrictNormalHom_ker]
  simp only [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

/-- Integer degree is equivalent to the arithmetic Frobenius power at every constant stage. -/
theorem fullConstantDegreeData_eq_int_iff (σ : Gal(Ω/K)) (z : ℤ) :
    (fullConstantDegreeData k K Ω).degree σ = Multiplicative.ofAdd (z : ZHat) ↔
      ∀ n : ℕ+, AlgEquiv.restrictNormalHom (fullConstantDegreeStage k K Ω n) σ =
        fullConstantDegreeFrobenius k K Ω n ^ z := by
  obtain ⟨φ, hφ, hr⟩ := exists_fullConstantFrobenius_lift k K Ω
  have hd : (fullConstantDegreeData k K Ω).degree (φ ^ z) =
      Multiplicative.ofAdd (z : ZHat) := by
    rw [map_zpow, hφ]
    apply Multiplicative.ext
    change z • (1 : ZHat) = (z : ZHat)
    rw [zsmul_eq_mul, mul_one]
  rw [← hd, fullConstantDegreeData_eq_iff_restrict]
  exact forall_congr' fun n => by rw [map_zpow, hr n]

end FunctionField
