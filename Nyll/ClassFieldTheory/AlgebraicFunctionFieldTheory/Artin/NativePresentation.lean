/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.GaloisPresentationValue
import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationIndependence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical

/-!
# Native reciprocity under an actual separable-closure presentation

An actual isomorphism with a finite fixed field determines its closed fixing
subgroup. Normality identifies that subgroup with the canonical realization,
so native reciprocity can be evaluated using the given fixed-field presentation.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory CyclicCohomology

/-- The fixed-field presentation and the given embedding induce the same
finite Galois quotient action. -/
theorem presentedGaloisQuotientOfEmbedding
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    let Ω := SeparableClosure K
    let H := intrinsicFiniteAbstractBase K
    let T := finiteGaloisAbstractExtensionOfEmbedding K L i
    let eE := finiteGaloisEmbeddedFixedFieldEquiv K L i
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω T.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    ∀ q : T.extensionQuotient,
      (AlgEquiv.autCongr eE).symm
          ((abstractExtensionQuotientEquivGaloisGroup
            K Ω H.field T.field T.below T.normal q).restrictScalars K) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q := by
  intro Ω H T eE aFE hKFE q
  have hF : Module.finrank K (abstractFixedField K Ω H.field) = 1 := by
    rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq, Module.finrank_self]
  refine QuotientGroup.induction_on q ?_
  intro τ
  apply AlgEquiv.ext
  intro x
  apply i.injective
  have hleft := ClassFieldTheory.galoisPresentation_mk_apply_val
    K L Ω H.field T.field T.below T.normal eE hF τ x
  dsimp only [Ω, H, T] at hleft
  change i ((AlgEquiv.autCongr eE).symm
      ((abstractExtensionQuotientEquivGaloisGroup
        K Ω H.field T.field T.below T.normal (QuotientGroup.mk τ)).restrictScalars K) x) =
    τ.val (i x) at hleft
  exact hleft.trans
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K L i τ x).symm


private theorem finiteGaloisAbstractExtension_eq_of_fixedFieldEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (T : FiniteGaloisSubextension (intrinsicFiniteAbstractBase K).field)
    (eE : L ≃ₐ[K] abstractFixedField K (SeparableClosure K) T.field) :
    T = finiteGaloisAbstractExtension K L := by
  let Ω := SeparableClosure K
  let E := abstractFixedField K Ω T.field
  let i : L →ₐ[K] Ω := E.val.comp eE.toAlgHom
  let j := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  have hi : i.fieldRange = E := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (eE y).property
    · intro x hx
      obtain ⟨y, hy⟩ := eE.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have ht : T.field = (finiteGaloisAbstractExtension K L).field := by
    calc
      T.field = RamificationTheory.closedFixingSubgroup K Ω E :=
        (closedFixingSubgroup_abstractFixedField_eq K Ω T.field).symm
      _ = RamificationTheory.closedFixingSubgroup K Ω i.fieldRange := congrArg
        (RamificationTheory.closedFixingSubgroup K Ω) hi.symm
      _ = RamificationTheory.closedFixingSubgroup K Ω j.fieldRange := congrArg
        (RamificationTheory.closedFixingSubgroup K Ω)
        (ClassFieldTheory.fieldRange_eq_of_normal i j)
      _ = _ := rfl
  have hext : ∀ A B : FiniteGaloisSubextension (intrinsicFiniteAbstractBase K).field,
      A.field = B.field → A = B := by
    rintro ⟨A, hA, hAn, hAf⟩ ⟨B, hB, hBn, hBf⟩ h
    cases h
    rfl
  exact hext T (finiteGaloisAbstractExtension K L) ht

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [akΩ : Algebra k (SeparableClosure K)]
    [aRΩ : Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

/-- An actual fixed-field presentation gives the native finite Artin value. -/
theorem finiteArtin_eq_fixedFieldPresentation
    (T : FiniteGaloisSubextension (intrinsicFiniteAbstractBase K).field)
    (eE : L ≃ₐ[K] abstractFixedField K (SeparableClosure K) T.field)
    (c : IdeleClassGroup k K) :
    let Ω := SeparableClosure K
    finiteArtin k K L c =
      normQuotientEquivOfFixedFieldPresentation k K L Ω
        (intrinsicFiniteAbstractBase K) T (finiteGaloisBaseFixedFieldEquiv K) eE
        (QuotientGroup.mk c) := by
  have hak : akΩ =
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra :=
    Algebra.algebra_ext akΩ _ (fun x => IsScalarTower.algebraMap_apply k K
      (SeparableClosure K) x)
  subst akΩ
  have haR : aRΩ =
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra :=
    Algebra.algebra_ext aRΩ _ (fun x => IsScalarTower.algebraMap_apply (RatFunc k) K
      (SeparableClosure K) x)
  subst aRΩ
  let akCanonical : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRCanonical : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  intro Ω
  have hT := finiteGaloisAbstractExtension_eq_of_fixedFieldEquiv K L T eE
  subst T
  let H := intrinsicFiniteAbstractBase K
  let T := finiteGaloisAbstractExtension K L
  let eF := finiteGaloisBaseFixedFieldEquiv K
  let eC := finiteGaloisFixedFieldEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)
  have h := congrArg
    (fun f : (IdeleClassGroup k K ⧸
        (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
          Abelianization Gal(L/K) => f (QuotientGroup.mk c))
    (normQuotientEquivOfFixedFieldPresentation_eq k K L Ω H T eF eF eC eE)
  change finiteNormQuotientEquiv k K L (QuotientGroup.mk c) = _
  dsimp only [finiteNormQuotientEquiv, finiteNormQuotientEquivOfEmbedding]
  with_reducible exact h


/-- On an actual intrinsic fixed field, presentation transport is just scalar restriction. -/
theorem finiteArtin_eq_intrinsicFixedField_restrict
    (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K] :
    let _ : CommSemiring (SeparableClosure K) :=
      (inferInstance : Field (SeparableClosure K)).toSemifield.toCommSemiring
    ∀ [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]
    (S : ClosedSubgroup Gal(SeparableClosure K/K))
    (hSB : S.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup)
    [hSnormal : (CyclicCohomology.extensionSubgroup
      (intrinsicFiniteAbstractBase K).field S hSB).Normal]
    [hSfinite : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      CyclicCohomology.extensionSubgroup (intrinsicFiniteAbstractBase K).field S hSB)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) S)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) S)]
    [AlgebraicCurve.HasPrincipalDivisors k
      (abstractFixedField K (SeparableClosure K) S)],
    let _ : CommSemiring (abstractFixedField K (SeparableClosure K) S) :=
      (inferInstance : Field (abstractFixedField K (SeparableClosure K) S)).toSemifield
        |>.toCommSemiring
    let aBE : Algebra
        (abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field)
        (abstractFixedField K (SeparableClosure K) S) :=
      (abstractRelativeFixedField K (SeparableClosure K) hSB).algebra
    let _ : SMul
        (abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field)
        (abstractFixedField K (SeparableClosure K) S) := aBE.toSMul
    have _ : IsScalarTower K
        (abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field)
        (abstractFixedField K (SeparableClosure K) S) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K)
        (intrinsicFiniteAbstractBase K).field) :=
      (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finiteDimensional
    ∀ c : IdeleClassGroup k K,
      finiteArtin k K (abstractFixedField K (SeparableClosure K) S) c =
        Abelianization.map
          (AlgEquiv.restrictScalarsHom
            (S := abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field)
            (A := abstractFixedField K (SeparableClosure K) S) K :
            Gal((abstractFixedField K (SeparableClosure K) S)/
              (abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field)) →*
            Gal((abstractFixedField K (SeparableClosure K) S)/K))
          (fixedFieldArtin k K (SeparableClosure K) (intrinsicFiniteAbstractBase K)
            ⟨S, hSB, hSnormal, hSfinite⟩
            (IdeleClassGroup.baseChange (k := k) (K := K)
              (L := abstractFixedField K (SeparableClosure K)
                (intrinsicFiniteAbstractBase K).field) c)) := by
  intro closureCommSemiring akΩ aRΩ hkKΩ hRKΩ hkRΩ S hSB hSnormal hSfinite
    hKSfinite hKSgal hKSprincipal cE aBE sBE hKBE hKF0 c
  let Ω := SeparableClosure K
  let B := intrinsicFiniteAbstractBase K
  let T : FiniteGaloisSubextension B.field := ⟨S, hSB, hSnormal, hSfinite⟩
  let F0 := abstractFixedField K Ω B.field
  let E := abstractFixedField K Ω S
  change IsScalarTower K F0 E at hKBE
  let eF0 := finiteGaloisBaseFixedFieldEquiv K
  have hKF0gal : IsGalois K F0 := IsGalois.of_algEquiv eF0
  have hF0 : Module.finrank K F0 = 1 := by
    rw [← eF0.toLinearEquiv.finrank_eq, Module.finrank_self]
  let eG : Gal(E/F0) ≃* Gal(E/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF0).trans
      (AlgEquiv.autCongr (AlgEquiv.refl : E ≃ₐ[K] E)).symm
  have nativeEvaluation :=
    finiteArtin_eq_fixedFieldPresentation k K E T (AlgEquiv.refl : E ≃ₐ[K] E)
  have presentationEvaluation := normQuotientEquivOfFixedFieldPresentation_mk
    k K E Ω B T eF0 (AlgEquiv.refl : E ≃ₐ[K] E)
  dsimp (config := { instances := true }) only [Ω, B, T, eF0]
    at nativeEvaluation presentationEvaluation
  let ρ : Gal(E/F0) →* Gal(E/K) := AlgEquiv.restrictScalarsHom K
  have hvalue (z : Abelianization Gal(E/F0)) :
      eG.abelianizationCongr z = Abelianization.map ρ z := by
    refine QuotientGroup.induction_on z ?_
    intro σ
    change Abelianization.of (eG σ) = Abelianization.of (σ.restrictScalars K)
    apply congrArg Abelianization.of
    apply AlgEquiv.ext
    intro x
    rfl
  exact ((nativeEvaluation c).trans (presentationEvaluation c)).trans (hvalue _)

end FunctionField
