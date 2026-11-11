/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantLocalization
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayPrincipalUnitValues
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Geometric orders and principal units of the native Artin-kernel limit

The normalized order at an actual geometric place is read directly from any
native finite-stage kernel representative. At a reduced boundary, triviality
of that representative's original local coordinate is exactly the geometric
residue-value-one condition. The comparisons retain the actual geometric field,
the original stage inclusions, and the original restricted-ray coordinates.
-/

@[expose] public section


noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "E" => geometricArtinStageField k K Ω
local notation "G" => geometricConstantExtension k K Ω
local notation "C" => separableClosure k Ω

local instance geometricLocalizationConstants : Algebra C G :=
  constantAlgebra (K := K) C

local instance geometricLocalizationConstantTower : IsScalarTower k C G :=
  constantScalarTower (K := K) C

local instance geometricLocalizationStageAlgebra (i : GeometricArtinIndex k K Ω) :
    Algebra (E i) G :=
  (fullConstantStageGeometricInclusion k K Ω i.degree).toRingHom.toAlgebra

local instance geometricLocalizationStageTower (i : GeometricArtinIndex k K Ω) :
    IsScalarTower K (E i) G :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

local instance geometricLocalizationBaseStageTower (i : GeometricArtinIndex k K Ω) :
    IsScalarTower k (E i) G :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

local instance geometricLocalizationRatFuncAlgebra (i : GeometricArtinIndex k K Ω) :
    Algebra (RatFunc k) (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).val

local instance geometricLocalizationRatFuncTower (i : GeometricArtinIndex k K Ω) :
    IsScalarTower k (RatFunc k) (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).property.1

local instance geometricLocalizationFunctionField (i : GeometricArtinIndex k K Ω) :
    FunctionField k (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).property.2

local instance geometricLocalizationPrincipalDivisors (i : GeometricArtinIndex k K Ω) :
    HasPrincipalDivisors k (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K (E i)).toHasPrincipalDivisors

/-- The actual place of the finite constant stage below the given geometric
place. No chosen residue-field isomorphism enters this restriction. -/
def geometricArtinPlaceAtStage (i : GeometricArtinIndex k K Ω) (W : Place C G) :
    Place k (E i) :=
  algebraicConstantPlaceRestrict (K := K) C (E i) W

/-- The original stage inclusion preserves the geometric normalized order. -/
theorem geometricArtinPlaceAtStage_order
    (i : GeometricArtinIndex k K Ω) (W : Place C G) (x : E i) :
    W.ord (fullConstantStageGeometricInclusion k K Ω i.degree x) =
      (geometricArtinPlaceAtStage k K Ω i W).ord x :=
  algebraicConstantPlaceRestrict_order (K := K) C (E i) W x

/-- Pulling the boundary through a finite constant stage gives exactly the
boundary exponent at the original place below the same geometric point. -/
theorem geometricArtinPlaceAtStage_modulus
    (m : Modulus k K) (i : GeometricArtinIndex k K Ω) (W : Place C G) :
    rayModulusBaseChange (E i) m (geometricArtinPlaceAtStage k K Ω i W) =
      m (algebraicConstantPlaceRestrict (K := K) C K W) := by
  rw [rayModulusBaseChange_apply]
  exact congrArg (fun v : Place k K => m v)
    (algebraicConstantPlaceRestrict_restrict (K := K) C (E i) W)

/-- Every native representative computes exactly the normalized order of its
function under the geometric Artin-kernel equivalence. -/
theorem geometricArtinKernelEquiv_mk_order
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (a : GeometricArtinStageKernel k K Ω m i)
    (W : Place C G) :
    W.ord (geometricArtinKernelEquiv k K Ω m hm hmzero ⟦⟨i, a⟩⟧ : G) =
      (restrictedRayOrder (rayModulusBaseChange (E i) m)
        (geometricArtinPlaceAtStage k K Ω i W) a.val).toAdd := by
  obtain ⟨x, rfl⟩ := (principalRestrictedArtinKernelEquiv
    (rayModulusBaseChange (E i) m) (rayModulusBaseChange_ne_zero m hmzero)).surjective a
  rw [geometricArtinKernelEquiv_principal,
    restrictedRayOrder_principalRestrictedArtinKernelEquiv]
  exact geometricArtinPlaceAtStage_order k K Ω i W (x : E i)

/-- At a reduced boundary, the actual finite-stage local coordinate is the
full principal-unit condition on the resulting geometric function. -/
theorem geometricArtinKernelEquiv_mk_boundary
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (a : GeometricArtinStageKernel k K Ω m i)
    (W : Place C G)
    (hW : m (algebraicConstantPlaceRestrict (K := K) C K W) = 1) :
    a.val (geometricArtinPlaceAtStage k K Ω i W) = 1 ↔
      W.HasValue (geometricArtinKernelEquiv k K Ω m hm hmzero ⟦⟨i, a⟩⟧ : G) 1 := by
  obtain ⟨x, rfl⟩ := (principalRestrictedArtinKernelEquiv
    (rayModulusBaseChange (E i) m) (rayModulusBaseChange_ne_zero m hmzero)).surjective a
  have hi : rayModulusBaseChange (E i) m (geometricArtinPlaceAtStage k K Ω i W) = 1 :=
    (geometricArtinPlaceAtStage_modulus k K Ω m i W).trans hW
  rw [principalRestrictedArtinKernelEquiv_boundary _ _ _ _ hi,
    completion_mem_localHigherUnitGroup_one_iff_hasValue,
    geometricArtinKernelEquiv_principal]
  have hvalue := algebraicConstantPlaceRestrict_hasValue (K := K)
    C (E i) W (x : E i) (1 : k)
  change (algebraicConstantPlaceRestrict (K := K) C (E i) W).HasValue (x : E i) 1 ↔
    W.HasValue (algebraMap (E i) G (x : E i)) 1
  simpa only [map_one] using hvalue.symm

/-- Normalized orders computed in different native stages are independent of
the representative in the original Artin-kernel direct limit. -/
theorem geometricArtinKernel_order_independent
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i j : GeometricArtinIndex k K Ω)
    (a : GeometricArtinStageKernel k K Ω m i)
    (b : GeometricArtinStageKernel k K Ω m j)
    (h : (⟦⟨i, a⟩⟧ : GeometricArtinKernel k K Ω m hm hmzero) = ⟦⟨j, b⟩⟧)
    (W : Place C G) :
    (restrictedRayOrder (rayModulusBaseChange (E i) m)
      (geometricArtinPlaceAtStage k K Ω i W) a.val).toAdd =
      (restrictedRayOrder (rayModulusBaseChange (E j) m)
        (geometricArtinPlaceAtStage k K Ω j W) b.val).toAdd := by
  rw [← geometricArtinKernelEquiv_mk_order k K Ω m hm hmzero i a W,
    ← geometricArtinKernelEquiv_mk_order k K Ω m hm hmzero j b W, h]

/-- The full boundary principal-unit predicate is independent of the original
finite-stage representative at each point over the original reduced boundary. -/
theorem geometricArtinKernel_boundary_independent
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i j : GeometricArtinIndex k K Ω)
    (a : GeometricArtinStageKernel k K Ω m i)
    (b : GeometricArtinStageKernel k K Ω m j)
    (h : (⟦⟨i, a⟩⟧ : GeometricArtinKernel k K Ω m hm hmzero) = ⟦⟨j, b⟩⟧)
    (W : Place C G)
    (hW : m (algebraicConstantPlaceRestrict (K := K) C K W) = 1) :
    a.val (geometricArtinPlaceAtStage k K Ω i W) = 1 ↔
      b.val (geometricArtinPlaceAtStage k K Ω j W) = 1 := by
  rw [geometricArtinKernelEquiv_mk_boundary k K Ω m hm hmzero i a W hW,
    geometricArtinKernelEquiv_mk_boundary k K Ω m hm hmzero j b W hW, h]

end FunctionField.RayClass
