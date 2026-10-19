/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPowerRay
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Actual Kummer norm groups inside ray-power subgroups

The finite set is supplied by the Picard presentation and the modulus.
Its actual S-unit root extension has norm image equal to the local-power
subgroup, which lies inside the prescribed ray-power subgroup.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [IsSepClosure K Ω]

/-- A ray-power subgroup contains an actual finite abelian norm group when
the required roots of unity lie in the base field. -/
theorem exists_finiteAbelian_norm_le_rayPower_of_roots
    (m : RayClass.Modulus k K) (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ E : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K E ∧
      (have _ : HasPrincipalDivisors k E :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ≤
        RayClass.powerRaySubgroup m (n : ℕ)) := by
  obtain ⟨S, hSne, hS, hray⟩ := IdeleGroup.exists_supported_powerClassSubgroup_le m n
  let E := SUnits.kummerExtension (Ω := Ω) n S
  have hEfinite : FiniteDimensional K E := SUnits.kummerExtension_finiteDimensional n hn hmu S
  have hEabelian : IsAbelianGalois K E :=
    KummerTheory.kummerRadicalExtension_isAbelianGalois n hmu (SUnits.units k K S)
  let Ef : FiniteGaloisIntermediateField K Ω := { toIntermediateField := E }
  refine ⟨Ef, hEabelian, ?_⟩
  intro hEprincipal
  have hnorm := SUnits.kummerExtension_norm_range (Ω := Ω) n hn hmu S hSne hS
  exact hnorm.le.trans hray

end FunctionField
