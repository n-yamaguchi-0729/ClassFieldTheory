/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation
import Nyll.GaloisCohomology.Kummer.Abstract.MultiplicativeFixedPoints

/-!
# The actual function-field idele-class representation

The coefficients are the existing direct limit of finite-extension idele
classes. Fixed coefficients over a finite abstract field are identified with
the actual idele classes of its concrete fixed field by proved Galois descent.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open IdeleClassGroup.FiniteExtensionLimit

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]

/-- The actual absolute idele-class module, written additively for cohomology. -/
def ideleClassRepresentation : Rep ℤ Gal(Ω/K) :=
  Rep.ofMulDistribMulAction Gal(Ω/K) (Limit k K Ω)

variable [IsGalois K Ω]

/-- Actual idele classes are exactly the coefficients fixed by the corresponding
finite abstract field, with no normality requirement on that field. -/
def abstractFixedClassEquiv (H : ClosedSubgroup Gal(Ω/K))
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H) :=
      abstractFixedField_finiteDimensional K Ω H hfinite
    Additive (IdeleClassGroup k (abstractFixedField K Ω H)) ≃+
      ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) H := by
  intro hFfinite
  let E := abstractFixedField K Ω H
  have hfixed : E.fixingSubgroup = H.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField H
  let eH : FixedPoints.subgroup E.fixingSubgroup (Limit k K Ω) ≃*
      FixedPoints.subgroup H.toSubgroup (Limit k K Ω) :=
    MulEquiv.subgroupCongr (congrArg
      (fun S : Subgroup Gal(Ω/K) => FixedPoints.subgroup S (Limit k K Ω)) hfixed)
  let e := (intermediateEquivFixed (k := k) E).trans eH
  exact (MulEquiv.toAdditive e).trans
    (multiplicativeFixedPointsEquiv Gal(Ω/K) (Limit k K Ω) H)

/-- The fixed coefficient comparison is the original inclusion into the direct limit. -/
theorem abstractFixedClassEquiv_coe (H : ClosedSubgroup Gal(Ω/K))
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H) :=
      abstractFixedField_finiteDimensional K Ω H hfinite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H)),
      (abstractFixedClassEquiv k K Ω H hfinite c).1 =
        Additive.ofMul (ofIntermediate (k := k) (abstractFixedField K Ω H) c.toMul) := by
  intro hFfinite c
  rfl

end FunctionField
