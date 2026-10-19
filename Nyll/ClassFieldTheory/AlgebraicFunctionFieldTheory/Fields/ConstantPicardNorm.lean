/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGeneration
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteConstantNorm
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindexNorm

/-!
# The actual Picard norm image of the constructed constant extension

Apply the proved norm criterion to the actual constant compositum. Reindexing
by the original full constants gives the normalized degree formula even when
the initially specified finite base field is smaller than the full constants.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- The actual Picard norm image is exactly divisibility of degree over the full constants. -/
theorem mem_picardNorm_fullConstantDegreeStage_iff (n : ℕ) [NeZero n] (x : Pic k K) :
    x ∈ (Pic.norm (k := k) (K := K) (L := fullConstantDegreeStage k K Ω n)).range ↔
      (n : ℤ) ∣ H1Gm.degree k K x / (Module.finrank k (algebraicClosure k K) : ℤ) := by
  have hft : Algebra.EssFiniteType k K := essFiniteType k K
  have hfinite : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let C := algebraicClosure k K
  let E := (finiteConstantsInClosure C Ω n).toIntermediateField
  let L := IntermediateField.adjoin K (E : Set Ω)
  have hcurve : IsCurveOver C K := isCurveOver_fullConstants k K
  have heft : Algebra.EssFiniteType C K := Algebra.EssFiniteType.of_comp k C K
  have hE : Finite E := Module.finite_of_finite C
  let algE : Algebra E L := constantAlgebra (K := K) E
  have towerE : IsScalarTower C E L := constantScalarTower (K := K) E
  have hfin : FiniteDimensional K L :=
    (fullConstantDegreeStage k K Ω n).finiteDimensional
  have hgal : IsGalois K L := (fullConstantDegreeStage k K Ω n).isGalois
  have hprincipalBase : HasPrincipalDivisors k L :=
    (inferInstance : HasPrincipalDivisors k (fullConstantDegreeStage k K Ω n))
  have hprincipal : HasPrincipalDivisors C L := hasPrincipalDivisors_extendedConstants k C L
  have hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ :=
    constantExtension_adjoin_constants (K := K) E
  have hdeg : Module.finrank K L = Module.finrank C E :=
    (finrank_fullConstantDegreeStage k K Ω n).trans
      (finrank_finiteConstantsInClosure C Ω n).symm
  change x ∈ (Pic.norm (k := k) (K := K) (L := L)).range ↔ _
  rw [mem_picardNorm_range_iff_constantEquiv (C := C),
    Pic.mem_norm_range_iff_of_finite_constants (constantsAreBase_fullConstants k K) hgen hdeg]
  change (Module.finrank C (finiteConstantsInClosure C Ω n) : ℤ) ∣
    H1Gm.degree C K (picConstantEquiv k C K x) ↔ _
  rw [finrank_finiteConstantsInClosure, degree_picConstantEquiv k C K,
    Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (fullConstants_degree_pos k K).ne')]

end FunctionField
