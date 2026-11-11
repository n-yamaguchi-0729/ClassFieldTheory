/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTower
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange

/-!
# The original restricted-ray arrows between finite constant stages

These arrows are the actual completion-induced finite-extension maps followed
by the proved equality of iterated and direct boundary pullbacks. Their
restriction to the original Artin kernels is the already constructed native
kernel transition. Place restriction uses the same literal intermediate-field
inclusion; no independently chosen function-field comparison enters either
construction.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "I" => GeometricArtinIndex k K Ω
local notation "E" => geometricArtinStageField k K Ω

/-- The original restriction of a place between two ordered finite
constant stages. -/
def geometricArtinStagePlaceRestrict (i j : I) (hij : i ≤ j)
    (w : Place k (E j)) : Place k (E i) := by
  let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  exact w.restrict (E i)

/-- The original restricted-product inclusion between actual finite
constant stages, retaining the direct pullback of the original boundary. -/
def geometricRestrictedRayTransition (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) :
    RayRestrictedProduct (rayModulusBaseChange (E i) m) →*
      RayRestrictedProduct (rayModulusBaseChange (E j) m) := by
  let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  exact (rayModulusCongr (rayModulusBaseChange_trans (L := E i) (M := E j) m)).toMonoidHom.comp
    (restrictedRayBaseChange (L := E j) (rayModulusBaseChange (E i) m)
      (rayModulusBaseChange_reduced m hm))

/-- The native kernel transition is the restriction of the same original
restricted-product transition, including its literal modulus equality. -/
theorem geometricArtinTransition_coe
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) (a : GeometricArtinStageKernel k K Ω m i) :
    (geometricArtinTransition k K Ω m hm i j hij a).val =
      geometricRestrictedRayTransition k K Ω m hm i j hij a.val := by
  let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  exact principalArtinKernelCongr_coe
    (rayModulusBaseChange_trans (L := E i) (M := E j) m)
    (principalArtinKernelBaseChange (L := E j) (rayModulusBaseChange (E i) m)
      (rayModulusBaseChange_reduced m hm) a)

end FunctionField.RayClass
