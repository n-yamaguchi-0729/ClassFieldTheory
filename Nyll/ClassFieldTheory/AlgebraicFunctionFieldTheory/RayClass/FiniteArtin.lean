/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ExtensionConductor

/-!
# Ray class Artin maps and the actual extension conductor

For a finite abelian extension, a modulus admits an Artin map on its ray
class quotient exactly when it bounds the actual extension conductor.
Every such Artin map is surjective onto the actual relative Galois group.
-/

noncomputable section

namespace FunctionField.RayClass

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- A modulus bounds the conductor exactly when its ray subgroup has trivial Artin image. -/
theorem extensionConductor_le_iff_artin (m : Modulus k K) :
    extensionConductor (k := k) (K := K) (L := L) ≤ m ↔
      ∀ c ∈ rayClassSubgroup m, abelianFiniteArtin k K L c = 1 := by
  rw [extensionConductor_le_iff]
  constructor
  · intro h c hc
    exact (abelianFiniteArtin_eq_one_iff_mem_norm k K L c).mpr (h hc)
  · intro h c hc
    exact (abelianFiniteArtin_eq_one_iff_mem_norm k K L c).mp (h c hc)

/-- The ray class Artin homomorphism with values in the actual relative Galois group. -/
def rayClassArtin (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) :
    (IdeleClassGroup k K ⧸ rayClassSubgroup m) →* Gal(L/K) :=
  (abelianFiniteNormQuotientEquiv k K L).toMonoidHom.comp (rayToNormQuotient m hm)

/-- The ray class symbol agrees with the idele-class Artin symbol on representatives. -/
theorem rayClassArtin_mk (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (c : IdeleClassGroup k K) :
    rayClassArtin k K L m hm (QuotientGroup.mk c) = abelianFiniteArtin k K L c :=
  rfl

/-- Every actual Galois element is the Artin symbol of an admissible ray class. -/
theorem rayClassArtin_surjective (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) :
    Function.Surjective (rayClassArtin k K L m hm) :=
  (abelianFiniteNormQuotientEquiv k K L).surjective.comp (rayToNormQuotient_surjective m hm)

/-- Factorization of the actual Artin homomorphism through a ray quotient detects the conductor. -/
theorem exists_rayClassArtin_iff (m : Modulus k K) :
    (∃ φ : (IdeleClassGroup k K ⧸ rayClassSubgroup m) →* Gal(L/K),
      φ.comp (QuotientGroup.mk' (rayClassSubgroup m)) = abelianFiniteArtin k K L) ↔
        extensionConductor (k := k) (K := K) (L := L) ≤ m := by
  constructor
  · rintro ⟨φ, hφ⟩
    apply (extensionConductor_le_iff_artin k K L m).mpr
    intro c hc
    have h := DFunLike.congr_fun hφ c
    change φ (QuotientGroup.mk c) = abelianFiniteArtin k K L c at h
    rw [(QuotientGroup.eq_one_iff c).mpr hc, map_one] at h
    exact h.symm
  · intro hm
    refine ⟨rayClassArtin k K L m hm, ?_⟩
    apply MonoidHom.ext
    intro c
    exact rayClassArtin_mk k K L m hm c

end FunctionField.RayClass
