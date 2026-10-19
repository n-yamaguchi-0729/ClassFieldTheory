/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction

/-!
# Naturality of finite reciprocity under field isomorphisms

An algebra isomorphism of finite extensions identifies their Artin symbols
by conjugation of the actual relative Galois groups.
-/

noncomputable section

namespace FunctionField

open scoped IsMulCommutative

variable (k K L M : Type) [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra K M]
    [IsScalarTower k K L] [IsScalarTower k K M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k M]

/-- An isomorphism of finite Galois extensions transports the abelianized Artin symbol. -/
theorem finiteArtin_autCongr [IsGalois K L] [IsGalois K M]
    (e : L ≃ₐ[K] M) (c : IdeleClassGroup k K) :
    (AlgEquiv.autCongr e).abelianizationCongr (finiteArtin k K L c) =
      finiteArtin k K M c := by
  let aLM : Algebra L M := e.toRingHom.toAlgebra
  have hKLM : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  have hr (σ : Gal(M/K)) : AlgEquiv.restrictNormalHom L σ = (AlgEquiv.autCongr e).symm σ := by
    apply AlgEquiv.ext
    intro x
    apply e.injective
    exact (AlgEquiv.restrictNormal_commutes σ L x).trans (e.apply_symm_apply _).symm
  have hx (z : Abelianization Gal(M/K)) :
      (AlgEquiv.autCongr e).abelianizationCongr
        (Abelianization.map (AlgEquiv.restrictNormalHom L) z) = z := by
    refine QuotientGroup.induction_on z ?_
    intro σ
    change Abelianization.of (AlgEquiv.autCongr e (AlgEquiv.restrictNormalHom L σ)) =
      Abelianization.of σ
    rw [hr, MulEquiv.apply_symm_apply]
  rw [← finiteArtin_restrictNormal k K L M c]
  exact hx (finiteArtin k K M c)

/-- An isomorphism of finite abelian extensions conjugates their actual Artin automorphisms. -/
theorem abelianFiniteArtin_autCongr [IsAbelianGalois K L] [IsAbelianGalois K M]
    (e : L ≃ₐ[K] M) (c : IdeleClassGroup k K) :
    AlgEquiv.autCongr e (abelianFiniteArtin k K L c) = abelianFiniteArtin k K M c := by
  apply (Abelianization.equivOfComm (H := Gal(M/K))).injective
  change Abelianization.of (AlgEquiv.autCongr e (abelianFiniteArtin k K L c)) =
    Abelianization.of (abelianFiniteArtin k K M c)
  rw [← abelianizationCongr_of, abelianFiniteArtin_of, abelianFiniteArtin_of]
  exact finiteArtin_autCongr k K L M e c

end FunctionField
