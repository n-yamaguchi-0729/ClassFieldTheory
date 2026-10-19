/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteNormQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.PresentationIndependence

/-!
# Independence from the separable-closure embedding

Normality identifies all embedded copies with the same intermediate field.
The remaining change of parameterization acts by an inner automorphism on
the relative Galois group, which disappears in its abelianization.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The finite reciprocity isomorphism does not depend on the explicit embedding. -/
theorem finiteNormQuotientEquivOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K) :
    finiteNormQuotientEquivOfEmbedding k K L i = finiteNormQuotientEquivOfEmbedding k K L j := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) Ω := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap K Ω) (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  dsimp only [finiteNormQuotientEquivOfEmbedding]
  exact normQuotientEquivOfFixedFieldPresentation_eq k K L Ω
    (intrinsicFiniteAbstractBase K) (finiteGaloisAbstractExtension K L) _ _ _ _

/-- Every explicit realization gives the intrinsic finite norm-quotient isomorphism. -/
theorem finiteNormQuotientEquivOfEmbedding_eq_intrinsic
    (i : L →ₐ[K] SeparableClosure K) :
    finiteNormQuotientEquivOfEmbedding k K L i = finiteNormQuotientEquiv k K L :=
  finiteNormQuotientEquivOfEmbedding_eq k K L i
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

end FunctionField
