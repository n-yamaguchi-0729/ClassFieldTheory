/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddingIndependence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian

/-!
# Restriction in arbitrary finite Galois towers

Compatible separable-closure embeddings transport fixed-field restriction
to the original fields. Embedding independence identifies the resulting
maps with the intrinsic finite Artin maps.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

variable (k K L M : Type) [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]

/-- Compatible embeddings transport reciprocity along an arbitrary finite Galois tower. -/
theorem finiteNormQuotientEquivOfEmbedding_restrictNormal [IsGalois K L] [IsGalois K M]
    (iM : M →ₐ[K] SeparableClosure K) (c : IdeleClassGroup k K) :
    Abelianization.map (AlgEquiv.restrictNormalHom L)
        (finiteNormQuotientEquivOfEmbedding k K M iM (QuotientGroup.mk c)) =
      finiteNormQuotientEquivOfEmbedding k K L
        (iM.comp (IsScalarTower.toAlgHom K L M)) (QuotientGroup.mk c) := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) Ω := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap K Ω) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let iL := iM.comp (IsScalarTower.toAlgHom K L M)
  let H : FiniteAbstractField Gal(Ω/K) := intrinsicFiniteAbstractBase K
  let T : FiniteGaloisSubextension H.field := finiteGaloisAbstractExtension K L
  let S : FiniteGaloisSubextension H.field := finiteGaloisAbstractExtension K M
  have hST : S.field.toSubgroup ≤ T.field.toSubgroup :=
    finiteGaloisAbstractExtension_le_of_tower K L M
  let eF : K ≃ₐ[K] abstractFixedField K Ω H.field := finiteGaloisBaseFixedFieldEquiv K
  let eL : L ≃ₐ[K] abstractFixedField K Ω T.field :=
    finiteGaloisFixedFieldEquivOfEmbedding K L iL
  let eM : M ≃ₐ[K] abstractFixedField K Ω S.field :=
    finiteGaloisFixedFieldEquivOfEmbedding K M iM
  have hcomm (x : L) : eM (algebraMap L M x) =
      IntermediateField.inclusion (abstractFixedField_le K Ω hST) (eL x) :=
    finiteGaloisFixedFieldEquivOfEmbedding_tower K L M iM x
  dsimp only [finiteNormQuotientEquivOfEmbedding]
  have hr := normQuotientEquivOfFixedFieldPresentation_restrictNormal k K L M Ω
    H T S hST eF eL eM hcomm c
  with_reducible exact hr

/-- The finite Artin map commutes with actual restriction in every finite Galois tower. -/
theorem finiteArtin_restrictNormal [IsGalois K L] [IsGalois K M]
    (c : IdeleClassGroup k K) :
    Abelianization.map (AlgEquiv.restrictNormalHom L) (finiteArtin k K M c) =
      finiteArtin k K L c := by
  let iM := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K M
  let iL := iM.comp (IsScalarTower.toAlgHom K L M)
  change Abelianization.map (AlgEquiv.restrictNormalHom L)
      (finiteNormQuotientEquiv k K M (QuotientGroup.mk c)) =
    finiteNormQuotientEquiv k K L (QuotientGroup.mk c)
  rw [← finiteNormQuotientEquivOfEmbedding_eq_intrinsic k K M iM,
    ← finiteNormQuotientEquivOfEmbedding_eq_intrinsic k K L iL]
  exact finiteNormQuotientEquivOfEmbedding_restrictNormal k K L M iM c

/-- Finite abelian Artin maps commute with actual restriction of field automorphisms. -/
theorem abelianFiniteArtin_restrictNormal [IsAbelianGalois K L] [IsAbelianGalois K M]
    (c : IdeleClassGroup k K) :
    AlgEquiv.restrictNormalHom L (abelianFiniteArtin k K M c) =
      abelianFiniteArtin k K L c := by
  apply (Abelianization.equivOfComm (H := Gal(L/K))).injective
  change Abelianization.of (AlgEquiv.restrictNormalHom L (abelianFiniteArtin k K M c)) =
    Abelianization.of (abelianFiniteArtin k K L c)
  rw [← Abelianization.map_of, abelianFiniteArtin_of, abelianFiniteArtin_of]
  exact finiteArtin_restrictNormal k K L M c

end FunctionField
