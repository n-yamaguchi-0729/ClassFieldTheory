/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.Classification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate

/-!
# Actual class fields with prescribed ramification support

The local-global theorem supplies the conductor bound on ramification.
The only input restriction on the subgroup is the prescribed ray containment.
Actual class-field existence supplies the extension; no auxiliary pole remains.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- Every open finite-index subgroup containing a prescribed ray subgroup
has an actual class field unramified at every place outside that modulus. -/
theorem exists_classField_unramified_away
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K)))
    (m : RayClass.Modulus k K) (hm : RayClass.rayClassSubgroup m ≤ H) :
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
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E)
      (_ : IsAbelianGalois K E),
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = H ∧
        ∀ w : Place k E, w.restrict K ∉ m.support → w.ramificationIndex K = 1 := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  have hexists := exists_classField_of_open k K H hH
  dsimp only at hexists
  obtain ⟨E, hEfinite, hEabelian, hEnorm⟩ := hexists
  have hfunctionE : FunctionField k E :=
    IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
      (k := k) (K := K) (Ω := SeparableClosure K) E
  have hEprincipal : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  have hconductor : RayClass.extensionConductor (k := k) (K := K) (L := E) ≤ m := by
    apply (RayClass.extensionConductor_le_iff (k := k) (K := K) (L := E) m).mpr
    rw [hEnorm]
    exact hm
  exact ⟨E, hEfinite, hEabelian, hEnorm,
    fun w hw => RayClass.ramificationIndex_eq_one_of_not_mem_support m hconductor w hw⟩

end FunctionField
