/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Norm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassRelativeKernel

/-!
# Naturality of full ray class norms

The actual norm on full ray class groups commutes with modulus change and
with norms in a tower. Both identities retain the same idèle representative.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u v w

namespace RayClass

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Norm descent is natural when both ray moduli are enlarged. -/
theorem rayClassNorm_modulusProjection
    {m m' : Modulus K} {n n' : Modulus L}
    (h : n.NormCompatible m) (h' : n'.NormCompatible m')
    (hmm' : m ≤ m') (hnn' : n ≤ n') (q : RayClassGroup n') :
    ClassFieldTheory.originalRayClassModulusProjection K hmm'
        (rayClassNorm h' q) =
      rayClassNorm h
        (ClassFieldTheory.originalRayClassModulusProjection L hnn' q) := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective n'.congruenceSubgroup q
  rfl

variable {M : Type w} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

/-- Full ray class norms are transitive in a finite tower for compatible
moduli, using transitivity of the existing ordinary idèle-class norm. -/
theorem rayClassNorm_tower
    {m : Modulus K} {n : Modulus M} {s : Modulus L}
    (hnm : n.NormCompatible m) (hsn : s.NormCompatible n)
    (hsm : s.NormCompatible m) (q : RayClassGroup s) :
    rayClassNorm hnm (rayClassNorm hsn q) = rayClassNorm hsm q := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective s.congruenceSubgroup q
  simp only [rayClassNorm_mk]
  exact congrArg (QuotientGroup.mk' m.congruenceSubgroup)
    (ordinaryIdeleClassNorm_tower K M L c)

end RayClass
