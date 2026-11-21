/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.AbsoluteNormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm

/-!
# Norms on norm-one idele groups

The ordinary idele norm restricts to a homomorphism between the actual
norm-one idele subgroups.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace NumberField.IdeleGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The standard field norm restricts to the kernels of the absolute norms. -/
def normOneNorm : normOneSubgroup (K := L) →* normOneSubgroup (K := K) :=
  ((norm K L).comp (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K)) (fun a =>
      show absoluteNorm (norm K L a.1) = 1 from (absoluteNorm_norm K L a.1).trans a.2)

/-- The map on norm-one ideles is the ordinary norm on the underlying idele. -/
@[simp]
theorem normOneNorm_apply (a : normOneSubgroup (K := L)) :
    (normOneNorm K L a : IdeleGroup (𝓞 K) K) = norm K L a.1 := rfl

/-- The restricted norm on standard ideles is continuous for the subgroup topology. -/
theorem normOneNorm_continuous : Continuous (normOneNorm K L) :=
  ((norm_continuous K L).comp continuous_subtype_val).subtype_mk _

end NumberField.IdeleGroup

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The ordinary idèle norm carries norm-one idèles to norm-one idèles. -/
theorem norm_mem_normOneSubgroup
    (a : IdeleGroup L)
    (ha : a ∈ normOneSubgroup (K := L)) :
    norm K L a ∈ normOneSubgroup (K := K) := by
  change absoluteNorm (norm K L a) = 1
  change absoluteNorm a = 1 at ha
  rw [absoluteNorm_norm]
  exact ha

/-- The norm restricted to the subgroup of ideles of absolute norm one. -/
noncomputable abbrev normOneNorm : normOneSubgroup (K := L) →* normOneSubgroup (K := K) :=
  NumberField.IdeleGroup.normOneNorm K L

/-- Coercing the restricted norm-one map recovers the ordinary idèle norm. -/
@[simp]
theorem normOneNorm_apply
    (a : normOneSubgroup (K := L)) :
    (normOneNorm K L a : IdeleGroup K) =
      norm K L a.1 :=
  rfl

end IdeleGroup

end
