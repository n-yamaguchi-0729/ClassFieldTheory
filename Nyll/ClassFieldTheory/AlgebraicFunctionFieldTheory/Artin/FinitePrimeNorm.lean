/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldPrimeNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FrobeniusAuxiliaryField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormIsomorphism
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower

/-!
# Prime-norm values under native field presentations

Norm transitivity and the degree-one inverse identify the norm to the original
base with the norm to its actual fixed-field presentation. Thus the concrete
Frobenius prime-norm formula survives the presentation used by finite Artin.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

attribute [local instance]
  intrinsicFrobeniusAuxiliaryCommSemiring
  intrinsicFrobeniusAuxiliaryAlgebra
  intrinsicFrobeniusAuxiliarySMul
  intrinsicFrobeniusAuxiliaryModule
  intrinsicFrobeniusAuxiliaryConstantAlgebra

variable (k K L Ω : Type) [Field k] [Finite k] [Field K] [Field L] [Field Ω]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The norm of any actual normalized-degree-one class in the Frobenius
auxiliary field has the expected value after transporting reciprocity to
the original base and target fields. -/
theorem normQuotientEquivOfFixedFieldPresentation_primeNorm
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    [IsMulCommutative T.extensionQuotient]
    (eF : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE : L ≃ₐ[K] abstractFixedField K Ω T.field) :
    let _ : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below) := T.finite
    let D := fullConstantDegreeData k K Ω
    let R := H.toFiniteResidueAbstractField D
    ∀ σ : D.FrobeniusElements R T.field T.below,
      let S := D.frobeniusFixedField R T.field T.below σ
      let A : IntermediateField K Ω := intrinsicFrobeniusAuxiliaryField k K Ω H T σ
      let hSfinite := D.frobeniusFixedField_absoluteFinite H T.field T.below σ
      let _ : FiniteDimensional K A :=
        abstractFixedField_finiteDimensional K Ω S hSfinite
      ∀ c : IdeleClassGroup k A,
        (IdeleClassGroup.normalizedDegree (k := k) (K := A) c).toAdd = 1 →
        normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE
            (QuotientGroup.mk (IdeleClassGroup.norm (k := k) (K := K)
              (L := A) c)) =
          Abelianization.of ((AlgEquiv.autCongr eE).symm
            ((abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
              (D.frobeniusRestriction R T.field T.below σ)).restrictScalars K)) := by
  intro hTfinite D R σ S A hSfinite hKS c hc
  let F := abstractFixedField K Ω H.field
  let E := abstractFixedField K Ω T.field
  let aFE : Algebra F E := (abstractRelativeFixedField K Ω T.below).algebra
  have hKFE : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hKF : FiniteDimensional K F := abstractFixedField_finiteDimensional K Ω H.field H.finite
  have hKFgal : IsGalois K F := IsGalois.of_algEquiv eF
  have hF : Module.finrank K F = 1 := by
    rw [← eF.toLinearEquiv.finrank_eq, Module.finrank_self]
  let eG : Gal(E/F) ≃* Gal(L/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF).trans
      (AlgEquiv.autCongr eE).symm
  let hSH : S.toSubgroup ≤ H.field.toSubgroup :=
    D.frobeniusFixedField_le R T.field T.below σ
  let aFA : Algebra F A := (abstractRelativeFixedField K Ω hSH).algebra
  have hKFA : IsScalarTower K F A := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkFA : IsScalarTower k F A := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFAfinite : FiniteDimensional F A := FiniteDimensional.right K F A
  have hFAsep : Algebra.IsSeparable F A :=
    Algebra.isSeparable_tower_top_of_isSeparable (F := K) (L := F) A
  have hnorm : IdeleClassGroup.baseChange (k := k) (K := K) (L := F)
      (IdeleClassGroup.norm (k := k) (K := K) (L := A) c) =
        IdeleClassGroup.norm (k := k) (K := F) (L := A) c := by
    have h := IdeleClassGroup.norm_baseChange_of_vertical_finrank_one
      (k := k) (K := K) (L := A) (F := F) (E := A) hF (Module.finrank_self A) c
    simpa only [IdeleClassGroup.baseChange_self] using h
  let q : T.extensionQuotient := D.frobeniusRestriction R T.field T.below σ
  let eQ := abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
  have hprime : fixedFieldArtin k K Ω H T
      (IdeleClassGroup.norm (k := k) (K := F) (L := A) c) =
        Abelianization.of (eQ q) :=
    fixedFieldArtin_frobenius_primeNorm k K Ω H T σ c hc
  have hsymbol := normQuotientEquivOfFixedFieldPresentation_mk k K L Ω H T eF eE
    (IdeleClassGroup.norm (k := k) (K := K) (L := A) c)
  calc
    _ = eG.abelianizationCongr (fixedFieldArtin k K Ω H T
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := F)
          (IdeleClassGroup.norm (k := k) (K := K) (L := A) c))) := hsymbol
    _ = eG.abelianizationCongr (fixedFieldArtin k K Ω H T
        (IdeleClassGroup.norm (k := k) (K := F) (L := A) c)) := by rw [hnorm]
    _ = Abelianization.of (eG (eQ q)) :=
      (congrArg eG.abelianizationCongr hprime).trans (abelianizationCongr_of eG (eQ q))
    _ = _ := congrArg Abelianization.of
      (congrArg (AlgEquiv.autCongr eE).symm
        (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne_apply hF (eQ q)))

end FunctionField
