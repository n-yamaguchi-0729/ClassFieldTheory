/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels

/-!
# Actual finite restrictions of the absolute function-field Artin map

Every finite abelian intermediate field recovers its native Artin map by
restricting the absolute Artin value to that field.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

private theorem absoluteAbelianRestriction_finiteProjection (K : Type) [Field K]
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (x : localAbsoluteAbelianProfinite K) :
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) x =
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk x) := by
  refine QuotientGroup.induction_on x fun σ => ?_
  rw [absoluteAbelianRestriction_mk, absoluteFiniteQuotientEquiv_mk_mk]

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

private theorem absoluteArtin_finiteQuotientRestriction
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) (absoluteArtin k K c) =
      abelianFiniteArtin k K (absoluteFiniteQuotientField K N) c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  rw [absoluteAbelianRestriction_finiteProjection]
  exact (congrArg (absoluteFiniteQuotientEquiv K N)
    (absoluteArtin_finiteProjection k K N c)).trans
      ((absoluteFiniteQuotientEquiv K N).apply_symm_apply _)

/-- Restriction to any actual finite abelian subextension is its native finite Artin map. -/
theorem absoluteArtin_restriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (c : IdeleClassGroup k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    absoluteAbelianRestriction K E (absoluteArtin k K c) = abelianFiniteArtin k K E c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  generalize hN : absoluteAbelianRestrictionKernel K E = N
  have hfield : absoluteFiniteQuotientField K N = E := by
    rw [← hN, absoluteFiniteQuotientField_restrictionKernel]
  subst E
  exact absoluteArtin_finiteQuotientRestriction k K N c

end FunctionField
