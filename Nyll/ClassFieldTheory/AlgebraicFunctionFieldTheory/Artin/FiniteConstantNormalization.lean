/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationConstantSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddingIndependence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantPresentedFrobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantAbstractExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate

/-!
# Native Artin reciprocity on finite constant extensions

The native Artin map on the degree-n full-constant extension sends an
idele class to arithmetic Frobenius raised to its normalized degree.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Native reciprocity on the actual constant extension has arithmetic normalization. -/
theorem finiteArtin_fullConstant (n : ℕ) [NeZero n] (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    finiteArtin k K (fullConstantDegreeStage k K (SeparableClosure K) n) c =
      Abelianization.of ((fullConstantDegreeFrobenius k K (SeparableClosure K) n) ^
        (IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  let Ω := SeparableClosure K
  let E := fullConstantDegreeStage k K Ω n
  let H := intrinsicFiniteAbstractBase K
  let T := finiteGaloisAbstractExtension K E
  let eF := finiteGaloisBaseFixedFieldEquiv K
  let eE := finiteGaloisFixedFieldEquivOfEmbedding K E E.toIntermediateField.val
  have hu := finiteGaloisAbstractExtension_fullConstant_isUnramified k K n
  have hs := normQuotientEquivOfFixedFieldPresentation_unramified
    k K E Ω H T eF eE hu c
  have hφ := fullConstant_presentedFrobenius k K n
  have hz := congrArg (fun σ : Gal(E/K) => Abelianization.of
    (σ ^ (IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd)) hφ
  have he := congrArg (fun f :
      (IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range) ≃*
        Abelianization Gal(E/K) => f (QuotientGroup.mk c))
    (finiteNormQuotientEquivOfEmbedding_eq_intrinsic k K E E.toIntermediateField.val)
  apply he.symm.trans
  dsimp only [finiteNormQuotientEquivOfEmbedding]
  with_reducible exact hs.trans hz

/-- Native reciprocity equals the constant Frobenius character in the actual cyclic Galois group. -/
theorem abelianFiniteArtin_fullConstant (n : ℕ) [NeZero n] :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    let _ : IsCyclic Gal((fullConstantDegreeStage k K (SeparableClosure K) n)/K) :=
      isCyclic_fullConstantDegreeStage k K (SeparableClosure K) n
    let _ : IsAbelianGalois K (fullConstantDegreeStage k K (SeparableClosure K) n) :=
      IsAbelianGalois.of_isCyclic K (fullConstantDegreeStage k K (SeparableClosure K) n)
    abelianFiniteArtin k K (fullConstantDegreeStage k K (SeparableClosure K) n) =
      IdeleClassGroup.constantFrobeniusCharacter k K (SeparableClosure K) n := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hcyc hab
  apply MonoidHom.ext
  intro c
  apply (Abelianization.equivOfComm
    (H := Gal((fullConstantDegreeStage k K (SeparableClosure K) n)/K))).injective
  change Abelianization.of (abelianFiniteArtin k K
    (fullConstantDegreeStage k K (SeparableClosure K) n) c) = _
  rw [abelianFiniteArtin_of, finiteArtin_fullConstant]
  rfl

end FunctionField
