/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldPresentation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation

/-!
# Finite reciprocity for ordinary function-field extensions

An explicit separable-closure embedding identifies the two fixed fields with
the original fields by degree-one inclusions. Actual norm compatibility
transports the fixed-field reciprocity isomorphism to the original norm
quotient and the original relative Galois group.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Reciprocity on the actual norm quotient of a finite Galois function-field extension,
relative to an explicit embedding into the separable closure. -/
def finiteNormQuotientEquivOfEmbedding (i : L →ₐ[K] SeparableClosure K) :
    (IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
      Abelianization Gal(L/K) := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) Ω := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap K Ω) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  exact normQuotientEquivOfFixedFieldPresentation k K L Ω
    (intrinsicFiniteAbstractBase K) (finiteGaloisAbstractExtension K L)
    (finiteGaloisBaseFixedFieldEquiv K) (finiteGaloisFixedFieldEquivOfEmbedding K L i)

/-- Reciprocity for an arbitrary finite Galois function-field extension. -/
def finiteNormQuotientEquiv :
    (IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
      Abelianization Gal(L/K) :=
  finiteNormQuotientEquivOfEmbedding k K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

end FunctionField
