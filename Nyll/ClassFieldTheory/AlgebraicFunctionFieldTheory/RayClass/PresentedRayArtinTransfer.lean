/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentedAbsoluteArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.NativeRayArtinTransfer

/-!
# Original transfer on ray quotients of the actual upper field

The native reciprocity comparison for the original upper field proves
preservation of its actual reduced ray subgroup. Its quotient therefore
gives original transfer into that field's own ray quotient. Actual idele
representatives then prove the restricted-product inclusion square.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FunctionField.RayClass

open AlgebraicCurve ClassFormation LocalClassFieldTheory

variable (k : Type w) (K : Type u) (L : Type v) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [FiniteDimensional K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
  (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal]

attribute [local instance]
  presentedFixedFieldSeparableClosureAlgebra presentedFixedFieldSeparableClosureSMul

variable [Algebra L (abstractFixedField K (SeparableClosure K) H.field)]
  [IsScalarTower K L (abstractFixedField K (SeparableClosure K) H.field)]
  [Algebra L (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  [IsScalarTower L (abstractFixedField K (SeparableClosure K) H.field)
    (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  (hLF : Module.finrank L (abstractFixedField K (SeparableClosure K) H.field) = 1)
  (eF : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
    ≃ₐ[(abstractFixedField K (SeparableClosure K) H.field)] SeparableClosure K)
  (eL : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
    ≃ₐ[L] SeparableClosure L)

/-- Original transfer under an actual fixed-field presentation preserves
the original reduced ray subgroup of the actual upper field. -/
theorem presentedAbsoluteTransfer_mem_artinRaySubgroup
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : localAbsoluteAbelianProfinite K) (ha : a ∈ artinRaySubgroup m) :
    nativeAbsoluteTransferOfDegreeOnePresentation K L H hLF eF eL a ∈
      artinRaySubgroup (rayModulusBaseChange L m) := by
  obtain ⟨c, hc, rfl⟩ := ha
  refine ⟨IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c,
    baseChange_mem_reducedRayClassSubgroup m hm c hc, ?_⟩
  exact absoluteArtin_baseChange_presentedTransfer k K L H hLF eF eL c

/-- The original subgroup transfer descended to the actual upper field's
reduced ray quotient. -/
def nativeRayTransferOfDegreeOnePresentation
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) →ₜ*
      (localAbsoluteAbelianProfinite L ⧸ artinRaySubgroup (rayModulusBaseChange L m)) := by
  let t := nativeAbsoluteTransferOfDegreeOnePresentation K L H hLF eF eL
  let f := QuotientGroup.map (artinRaySubgroup m)
    (artinRaySubgroup (rayModulusBaseChange L m)) t.toMonoidHom
    (presentedAbsoluteTransfer_mem_artinRaySubgroup k K L H hLF eF eL m hm)
  refine { toMonoidHom := f, continuous_toFun := ?_ }
  rw [← (QuotientGroup.isOpenQuotientMap_mk
    (N := artinRaySubgroup m)).continuous_comp_iff]
  exact QuotientGroup.continuous_mk.comp t.continuous_toFun

/-- The ray transfer is the quotient of the literal native absolute transfer. -/
theorem nativeRayTransferOfDegreeOnePresentation_mk
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : localAbsoluteAbelianProfinite K) :
    nativeRayTransferOfDegreeOnePresentation k K L H hLF eF eL m hm
        (QuotientGroup.mk' (artinRaySubgroup m) a) =
      QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange L m))
        (nativeAbsoluteTransferOfDegreeOnePresentation K L H hLF eF eL a) := rfl

/-- Actual restricted-product inclusion commutes with original transfer
into the actual upper field, using native reciprocity at both ends. -/
theorem restrictedProductAbsoluteArtin_baseChange_presentedTransfer
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : RayRestrictedProduct m) :
    restrictedProductAbsoluteArtin (rayModulusBaseChange L m)
        (restrictedRayBaseChange (L := L) m hm a) =
      nativeRayTransferOfDegreeOnePresentation k K L H hLF eF eL m hm
        (restrictedProductAbsoluteArtin m a) := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedRayBaseChange_idele, restrictedProductAbsoluteArtin_idele,
    restrictedProductAbsoluteArtin_idele, nativeRayTransferOfDegreeOnePresentation_mk,
    ← IdeleClassGroup.baseChange_mk]
  exact congrArg (QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange L m)))
    (absoluteArtin_baseChange_presentedTransfer k K L H hLF eF eL (IdeleClassGroup.mk b))

end FunctionField.RayClass
