/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.IdeleClassNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Norm
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Pullback of ray characters along norms

The continuous full ray norm is induced by the ordinary idèle-class norm.
Pulling back a character commutes with descent to the full ray quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace RayClass

variable {K : Type*} {L : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {n : Modulus L} {m : Modulus K}

/-- The actual full ray class norm with its quotient-topology continuity. -/
def rayClassNormContinuousMonoidHom (h : n.NormCompatible m) :
    RayClassGroup n →ₜ* RayClassGroup m :=
  ProCGroups.QuotientGroup.mapContinuousMonoidHom
    (N := n.congruenceSubgroup)
    (M := m.congruenceSubgroup)
    (NumberField.IdeleClassGroup.normContinuousMonoidHom K L) h.congruenceSubgroup_le

/-- The continuous norm has the same underlying map as the algebraic ray norm. -/
theorem rayClassNormContinuousMonoidHom_toMonoidHom (h : n.NormCompatible m) :
    (rayClassNormContinuousMonoidHom h).toMonoidHom = rayClassNorm h :=
  rfl

variable {A : Type*} [Group A] [TopologicalSpace A]

/-- The norm pullback of a character trivial at `m` is trivial at `n`. -/
theorem Modulus.NormCompatible.rayClassCharacter_pullback_ker
    (h : n.NormCompatible m) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    (hχ : m.congruenceSubgroup ≤ χ.toMonoidHom.ker) :
    n.congruenceSubgroup ≤
      (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)).toMonoidHom.ker := by
  intro c hc
  exact hχ (h.congruenceSubgroup_le hc)

/-- Descent to the ray quotient commutes with pullback by the actual norm. -/
theorem rayClassCharacter_lift_norm (h : n.NormCompatible m)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    (hχ : m.congruenceSubgroup ≤ χ.toMonoidHom.ker) :
    (ProCGroups.QuotientGroup.liftₜ m.congruenceSubgroup χ hχ).comp
        (rayClassNormContinuousMonoidHom h) =
      ProCGroups.QuotientGroup.liftₜ n.congruenceSubgroup
        (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L))
        (h.rayClassCharacter_pullback_ker χ hχ) := by
  apply ContinuousMonoidHom.ext
  intro q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective n.congruenceSubgroup q
  rfl

end RayClass
