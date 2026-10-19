/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteConstantNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantDegreeCoordinates
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# The constant degree of absolute Artin reciprocity

The continuous full-constant degree descends to the absolute topological
abelianization. Applied to the absolute Artin symbol, it is the integer
normalized idele-class degree embedded in the profinite integers.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The actual arithmetic constant degree on the absolute topological abelianization. -/
def absoluteAbelianDegree : localAbsoluteAbelianProfinite K →ₜ* ZHatMul :=
  ProCGroups.Abelian.TopologicalAbelianization.lift
    (fullConstantDegreeData k K (SeparableClosure K)).degree

/-- Every profinite arithmetic degree occurs in the absolute abelian Galois group. -/
theorem absoluteAbelianDegree_surjective : Function.Surjective (absoluteAbelianDegree k K) := by
  intro z
  obtain ⟨σ, hσ⟩ := (fullConstantDegreeData k K (SeparableClosure K)).degree_surjective z
  exact ⟨QuotientGroup.mk σ, hσ⟩

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Absolute reciprocity sends normalized integer degree to the actual profinite constant degree. -/
theorem absoluteAbelianDegree_artin (c : IdeleClassGroup k K) :
    absoluteAbelianDegree k K (absoluteArtin k K c) =
      Multiplicative.ofAdd ((IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd :
        ZHat) := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  obtain ⟨σ, hσ⟩ := ProCGroups.Abelian.TopologicalAbelianization.surjective_mk
    Gal((SeparableClosure K)/K) (absoluteArtin k K c)
  have hd : (fullConstantDegreeData k K (SeparableClosure K)).degree σ =
      Multiplicative.ofAdd ((IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd :
        ZHat) := by
    apply (fullConstantDegreeData_eq_int_iff k K (SeparableClosure K) σ _).2
    intro n
    let E := fullConstantDegreeStage k K (SeparableClosure K) n
    have hcyc : IsCyclic Gal(E/K) := isCyclic_fullConstantDegreeStage k K (SeparableClosure K) n
    have hab : IsAbelianGalois K E := IsAbelianGalois.of_isCyclic K E
    have hres := absoluteArtin_restriction k K E.toIntermediateField c
    have hnat := DFunLike.congr_fun (abelianFiniteArtin_fullConstant k K n) c
    have hq := congrArg (absoluteAbelianRestriction K E.toIntermediateField) hσ
    change absoluteAbelianRestriction K E.toIntermediateField (QuotientGroup.mk σ) = _ at hq
    rw [absoluteAbelianRestriction_mk] at hq
    exact hq.trans (hres.trans hnat)
  exact (congrArg (absoluteAbelianDegree k K) hσ.symm).trans hd

end FunctionField
