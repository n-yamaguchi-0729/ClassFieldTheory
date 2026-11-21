/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.Characters
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNorm

/-!
# Norm and restriction for the character correspondence

The specified global character equivalence commutes with the actual
idèle-class norm and the original absolute Galois restriction. Totally
disconnected targets include, in particular, all finite discrete targets.
-/

@[expose] public section

open scoped NumberField
open ProCGroups.Abelian

noncomputable section

universe u v w

namespace GlobalClassFieldTheory.Reciprocity

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {A : Type w} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [TotallyDisconnectedSpace A]

/-- Restricting an absolute Galois character corresponds to pullback along
the actual norm, under the specified geometric reciprocity map. -/
theorem mathlibGlobalCharacterEquiv_norm
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A) :
    mathlibGlobalCharacterEquiv L
        (χ.comp (TopologicalAbelianization.map
          (Field.absoluteGaloisGroup.map (algebraMap K L)))) =
      (mathlibGlobalCharacterEquiv K χ).comp
        (NumberField.IdeleClassGroup.normContinuousMonoidHom K L) := by
  apply ContinuousMonoidHom.ext
  intro c
  exact congrArg χ (mathlibGlobalArtin_norm K L c)

/-- Lifting a norm-pulled-back idèle character gives its original Galois
lift restricted through the specified absolute Galois map. -/
theorem mathlibIdeleClassCharacterLift_norm
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    mathlibIdeleClassCharacterLift L
        (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)) =
      (mathlibIdeleClassCharacterLift K χ).comp
        (TopologicalAbelianization.map (Field.absoluteGaloisGroup.map (algebraMap K L))) := by
  apply ContinuousMonoidHom.ext
  intro σ
  obtain ⟨c, rfl⟩ := mathlibGlobalArtin_surjective L σ
  change mathlibIdeleClassCharacterLift L
      (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L))
      (mathlibGlobalArtin L c) =
    mathlibIdeleClassCharacterLift K χ
      (TopologicalAbelianization.map (Field.absoluteGaloisGroup.map (algebraMap K L))
        (mathlibGlobalArtin L c))
  rw [mathlibIdeleClassCharacterLift_artin, mathlibGlobalArtin_norm,
    mathlibIdeleClassCharacterLift_artin]
  rfl

end GlobalClassFieldTheory.Reciprocity
