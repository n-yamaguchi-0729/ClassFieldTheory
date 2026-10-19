/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldRestriction
import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionTransport

/-!
# Restriction in compatible fixed-field presentations

The actual Galois restriction theorem transports through compatible field
isomorphisms and gives restriction compatibility on the original fields.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K L M Ω : Type)
    [Field k] [Finite k] [Field K] [Field L] [Field M] [Field Ω]
    [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Restriction of reciprocity is preserved by compatible fixed-field presentations. -/
theorem normQuotientEquivOfFixedFieldPresentation_restrictNormal
    (H : FiniteAbstractField Gal(Ω/K)) (T S : FiniteGaloisSubextension H.field)
    (hST : S.field.toSubgroup ≤ T.field.toSubgroup)
    (eF : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eL : L ≃ₐ[K] abstractFixedField K Ω T.field)
    (eM : M ≃ₐ[K] abstractFixedField K Ω S.field)
    (hcomm : ∀ x : L, eM (algebraMap L M x) =
      IntermediateField.inclusion (abstractFixedField_le K Ω hST) (eL x))
    (c : IdeleClassGroup k K) :
    Abelianization.map (AlgEquiv.restrictNormalHom L)
        (normQuotientEquivOfFixedFieldPresentation k K M Ω H S eF eM (QuotientGroup.mk c)) =
      normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eL (QuotientGroup.mk c) := by
  let F := abstractFixedField K Ω H.field
  let E := abstractFixedField K Ω T.field
  let U := abstractFixedField K Ω S.field
  have hKFfinite : FiniteDimensional K F := eF.toLinearEquiv.finiteDimensional
  have hKFgal : IsGalois K F := IsGalois.of_algEquiv eF
  let aFE : Algebra F E :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
  let aFU : Algebra F U :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω S.below)).toRingHom.toAlgebra
  let aEU : Algebra E U :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω hST)).toRingHom.toAlgebra
  have hKFE : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hKFU : IsScalarTower K F U := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFEU : IsScalarTower F E U := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFEgal : IsGalois F E :=
    abstractRelativeFixedField_isGalois K Ω H.field T.field T.below T.normal
  have hFdegree : Module.finrank K F = 1 := by
    rw [← eF.toLinearEquiv.finrank_eq, Module.finrank_self]
  let eGL : Gal(E/F) ≃* Gal(L/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
      (K := K) (F := F) (E := E) hFdegree).trans (AlgEquiv.autCongr eL).symm
  let eGM : Gal(U/F) ≃* Gal(M/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
      (K := K) (F := F) (E := U) hFdegree).trans (AlgEquiv.autCongr eM).symm
  let rL : Gal(M/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let rE : Gal(U/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  let d : IdeleClassGroup k F := IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c
  let zS : Abelianization Gal(U/F) := fixedFieldArtin k K Ω H S d
  let zT : Abelianization Gal(E/F) := fixedFieldArtin k K Ω H T d
  have hM := normQuotientEquivOfFixedFieldPresentation_mk k K M Ω H S eF eM c
  have hL := normQuotientEquivOfFixedFieldPresentation_mk k K L Ω H T eF eL c
  have htransport := ClassFieldTheory.abelianization_restrictNormal_transport
    (K := K) (F := F) (E := E) (U := U) hFdegree eL eM hcomm zS
  have hambient := fixedFieldArtin_restrictNormal k K Ω H T S hST d
  calc
    Abelianization.map rL
        (normQuotientEquivOfFixedFieldPresentation k K M Ω H S eF eM
          (QuotientGroup.mk c)) =
        Abelianization.map rL (eGM.abelianizationCongr zS) :=
      congrArg (Abelianization.map rL) hM
    _ = eGL.abelianizationCongr (Abelianization.map rE zS) := htransport
    _ = eGL.abelianizationCongr zT := congrArg eGL.abelianizationCongr hambient
    _ = normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eL
        (QuotientGroup.mk c) := hL.symm

end FunctionField
