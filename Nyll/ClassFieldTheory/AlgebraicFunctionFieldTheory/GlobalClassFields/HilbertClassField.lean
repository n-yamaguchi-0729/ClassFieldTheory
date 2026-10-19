/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SplitRayQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormUniqueness
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSplitting
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Conductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension

/-!
# Hilbert class fields with prescribed splitting places

The local-global Artin comparison identifies the local norm conditions.
The field is selected by the established ordinary-topology classification from the
zero-modulus ray subgroup with the prescribed local groups adjoined.
Nonemptiness of the splitting set supplies finite index.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace FunctionField

open AlgebraicCurve

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- Containing the prescribed zero-modulus subgroup means that every
place is unramified and each prescribed place splits completely. -/
theorem splitRaySubgroup_zero_le_norm_iff (S : Finset (Place k K))
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
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
    RayClass.splitRaySubgroup 0 S ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := E.val)).range ↔
      (∀ w : Place k E.val, w.ramificationIndex K = 1) ∧
      (∀ w : Place k E.val, w.restrict K ∈ S →
        w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  have hfunctionE : FunctionField k E.val :=
    IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
      (k := k) (K := K) (Ω := SeparableClosure K) E.val
  have hEprincipal : HasPrincipalDivisors k E.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E.val).toHasPrincipalDivisors
  constructor
  · intro h
    have hconductor : RayClass.extensionConductor (k := k) (K := K) (L := E.val) ≤ 0 := by
      apply (RayClass.extensionConductor_le_iff (k := k) (K := K) (L := E.val) 0).mpr
      exact (show RayClass.rayClassSubgroup 0 ≤ RayClass.splitRaySubgroup 0 S from
        le_sup_left).trans h
    refine ⟨fun w => RayClass.ramificationIndex_eq_one_of_not_mem_support
      0 hconductor w (Finsupp.notMem_support_iff.mpr rfl), ?_⟩
    intro w hw
    apply (localArtin_trivial_iff_completelySplit (K := K) w).mp
    intro x
    rw [localArtin_eq_abelianFiniteArtin_placeIdele k K E.val w x]
    exact (abelianFiniteArtin_eq_one_iff_mem_norm k K E.val _).mpr
      (h (RayClass.placeIdele_mem_splitRaySubgroup 0 S hw x))
  · rintro ⟨hunramified, hsplit⟩
    rw [RayClass.splitRaySubgroup]
    apply sup_le
    · apply (RayClass.extensionConductor_le_iff (k := k) (K := K) (L := E.val) 0).mp
      apply (RayClass.extensionConductor_le_iff_localConductor (L := E.val) 0).mpr
      intro w hrelation hlocal
      exact ((localConductorExponent_eq_zero_iff_ramificationIndex_eq_one
        (K := K) w).mpr (hunramified w)).le
    · apply iSup_le
      intro v
      apply iSup_le
      intro hv
      obtain ⟨w, hw⟩ := Place.exists_restrict_eq (M := E.val) v
      subst v
      rintro c ⟨x, rfl⟩
      apply (abelianFiniteArtin_eq_one_iff_mem_norm k K E.val _).mp
      exact (localArtin_eq_abelianFiniteArtin_placeIdele k K E.val w x).symm.trans
        ((localArtin_trivial_iff_completelySplit (K := K) w).mpr (hsplit w hv) x)

/-- The Hilbert class field is the largest finite abelian subextension
which is everywhere unramified and splits all prescribed places. -/
theorem le_hilbertClassField_iff (S : Finset (Place k K)) (hS : S.Nonempty)
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
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
    E.val ≤ (hilbertClassField k K S hS).val ↔
      (∀ w : Place k E.val, w.ramificationIndex K = 1) ∧
      (∀ w : Place k E.val, w.restrict K ∈ S →
        w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  have horder :
      (IdeleClassGroup.norm (k := k) (K := K)
        (L := (hilbertClassField k K S hS).val)).range ≤
          (IdeleClassGroup.norm (k := k) (K := K) (L := E.val)).range ↔
        E.val ≤ (hilbertClassField k K S hS).val :=
    finiteAbelian_norm_range_le_iff k K (hilbertClassField k K S hS).val E.val
  have hnorm :
      (IdeleClassGroup.norm (k := k) (K := K)
        (L := (hilbertClassField k K S hS).val)).range = RayClass.splitRaySubgroup 0 S :=
    hilbertClassField_norm k K S hS
  have hsplit := splitRaySubgroup_zero_le_norm_iff k K S E
  rw [← horder, hnorm]
  exact hsplit

/-- The selected Hilbert class field itself has the required unramified
and complete-splitting properties. -/
theorem hilbertClassField_spec (S : Finset (Place k K)) (hS : S.Nonempty) :
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
    (∀ w : Place k (hilbertClassField k K S hS).val, w.ramificationIndex K = 1) ∧
      (∀ w : Place k (hilbertClassField k K S hS).val, w.restrict K ∈ S →
        w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  exact (le_hilbertClassField_iff k K S hS (hilbertClassField k K S hS)).mp le_rfl

end FunctionField
