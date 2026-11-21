/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Factorization of characters through ray class groups

The modulus condition is containment of the existing ray congruence subgroup
in the character kernel. Descent uses the quotient topology and preserves the
value on every idele class. No finiteness or discreteness of the target is
needed for this universal property.
-/

@[expose] public section

open scoped NumberField Topology

namespace RayClass

variable {K : Type*} {A : Type*} [Field K] [NumberField K]
    [Group A] [TopologicalSpace A]

/-- A continuous character factors uniquely through the ray quotient precisely
when it kills the full ray congruence subgroup, including real positivity. -/
theorem existsUnique_rayClassCharacter_iff
    (m : Modulus K) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    (∃! ψ : RayClassGroup m →ₜ* A,
      ∀ c : NumberField.IdeleClassGroup (𝓞 K) K,
        ψ (QuotientGroup.mk' m.congruenceSubgroup c) = χ c) ↔
      m.congruenceSubgroup ≤ χ.toMonoidHom.ker := by
  constructor
  · rintro ⟨ψ, hψ, _⟩ c hc
    change χ c = 1
    have hq : QuotientGroup.mk' m.congruenceSubgroup c = 1 :=
      (QuotientGroup.eq_one_iff c).mpr hc
    exact (hψ c).symm.trans ((congrArg ψ hq).trans (map_one ψ))
  · intro hχ
    refine ⟨ProCGroups.QuotientGroup.liftₜ m.congruenceSubgroup χ hχ,
      fun _ => rfl, ?_⟩
    intro ψ hψ
    apply ContinuousMonoidHom.ext
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective m.congruenceSubgroup q
    exact hψ c

/-- Descent of a ray character commutes with postcomposition in its target. -/
theorem rayClassCharacter_lift_postcompose
    {B : Type*} [Group B] [TopologicalSpace B]
    (m : Modulus K) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    (hχ : m.congruenceSubgroup ≤ χ.toMonoidHom.ker)
    (f : A →ₜ* B) :
    f.comp (ProCGroups.QuotientGroup.liftₜ m.congruenceSubgroup χ hχ) =
      ProCGroups.QuotientGroup.liftₜ m.congruenceSubgroup (f.comp χ)
        (by
          intro c hc
          change f (χ c) = 1
          rw [show χ c = 1 from hχ hc, map_one]) := by
  apply ContinuousMonoidHom.ext
  intro q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective m.congruenceSubgroup q
  rfl

end RayClass
