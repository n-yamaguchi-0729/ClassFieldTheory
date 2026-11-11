/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricNativeRayTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FieldIsomorphismRayNaturality

/-!
# The original native deck operator at an actual constant stage

An original ambient Galois automorphism restricts to the actual finite
constant stage. Its original pulled-back boundary modulus is invariant
because its restriction to the original field is the identity. The native
field-isomorphism reciprocity map therefore gives an endomorphism of the
same original ray quotient, with literal semilinear conjugation on every
original absolute-abelian representative.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory KummerTheory

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
  [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
  [Algebra k Ω] [IsScalarTower k K Ω]
  (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
  (i : GeometricArtinIndex k K Ω) (σ : Gal(Ω/K))

local notation "L" => geometricArtinStageField k K Ω i
local notation "M" => rayModulusBaseChange L m
local notation "ε" => geometricNativeStageClosureEquiv k K Ω i
local notation "τ" => σ.restrictNormal L
local notation "hσ" => fun x : L =>
  Eq.symm (AlgEquiv.restrictNormal_commutes σ L x)
local notation "a" => nativeSemilinearClosureEquiv ε σ.toRingEquiv
local notation "ha" =>
  nativeSemilinearClosureEquiv_algebraMap ε (AlgEquiv.toRingEquiv τ) σ.toRingEquiv hσ
local notation "hM" => fieldIsoRayModulus_baseChange_of_fixed τ m

/-- The native ray operator of an actual original ambient automorphism,
on the unchanged original pulled-back boundary modulus. -/
def geometricNativeRayConjugation :
    (localAbsoluteAbelianProfinite L ⧸ artinRaySubgroup M) →ₜ*
      (localAbsoluteAbelianProfinite L ⧸ artinRaySubgroup M) :=
  fieldIsoNativeRayHom ((τ).restrictScalars k) M M
    (rayModulusBaseChange_reduced m hm) hM a ha

/-- Every original native absolute-abelian representative retains its
actual ambient semilinear conjugation. -/
theorem geometricNativeRayConjugation_mk (z : localAbsoluteAbelianProfinite L) :
    let abelianConjugation : localAbsoluteAbelianProfinite L ≃ₜ*
        localAbsoluteAbelianProfinite L :=
      nativeSemilinearAbsoluteAbelianEquiv ε (τ).toRingEquiv σ.toRingEquiv hσ
    geometricNativeRayConjugation k K Ω m hm i σ
        (QuotientGroup.mk' (artinRaySubgroup M) z) =
      QuotientGroup.mk' (artinRaySubgroup M) (abelianConjugation z) := by
  intro abelianConjugation
  have hRay := fieldIsoNativeRayHom_mk ((τ).restrictScalars k) M M
    (rayModulusBaseChange_reduced m hm) hM a ha z
  have hNative :
      nativeFieldIsoAbelianEquiv ((τ).restrictScalars k).toRingEquiv a ha =
        abelianConjugation :=
    nativeFieldIsoAbelianEquiv_eq_nativeSemilinear ε (τ).toRingEquiv σ.toRingEquiv hσ
  exact hRay.trans
    (congrArg (QuotientGroup.mk' (artinRaySubgroup M)) (DFunLike.congr_fun hNative z))

/-- The same native operator satisfies original reciprocity for the
actual field-isomorphism map on restricted products. -/
theorem geometricNativeRayConjugation_artin (z : RayRestrictedProduct M) :
    restrictedProductAbsoluteArtin M
        (fieldIsoRestrictedRayHom ((τ).restrictScalars k) M M
          (rayModulusBaseChange_reduced m hm) hM z) =
      geometricNativeRayConjugation k K Ω m hm i σ
        (restrictedProductAbsoluteArtin M z) :=
  fieldIsoNativeRayHom_artin ((τ).restrictScalars k) M M
    (rayModulusBaseChange_reduced m hm) hM a ha z

end FunctionField.RayClass
