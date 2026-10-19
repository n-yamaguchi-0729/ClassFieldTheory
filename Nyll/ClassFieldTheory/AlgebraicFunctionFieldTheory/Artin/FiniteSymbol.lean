/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteNormQuotient

/-!
# The finite function-field Artin homomorphism

The actual norm-quotient isomorphism gives a surjective homomorphism from
idele classes to the abelianized relative Galois group, with the actual
all-place norm image as kernel.
-/

noncomputable section

namespace FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The finite Artin homomorphism for the chosen separable-closure realization. -/
def finiteArtin : IdeleClassGroup k K →* Abelianization Gal(L/K) :=
  (finiteNormQuotientEquiv k K L).toMonoidHom.comp
    (QuotientGroup.mk' (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range)

/-- Every abelianized relative automorphism is represented by an idele class. -/
theorem finiteArtin_surjective : Function.Surjective (finiteArtin k K L) :=
  (finiteNormQuotientEquiv k K L).surjective.comp QuotientGroup.mk_surjective

/-- The finite Artin symbol is trivial exactly on actual norms. -/
theorem finiteArtin_eq_one_iff_mem_norm (c : IdeleClassGroup k K) :
    finiteArtin k K L c = 1 ↔
      c ∈ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  change finiteNormQuotientEquiv k K L (QuotientGroup.mk c) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff c

/-- The kernel is the actual all-place class norm subgroup. -/
theorem finiteArtin_ker : (finiteArtin k K L).ker =
    (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  apply Subgroup.ext
  intro c
  exact finiteArtin_eq_one_iff_mem_norm k K L c

end FunctionField
