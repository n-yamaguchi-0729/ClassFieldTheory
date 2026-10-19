/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.KummerRayExistence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormRefinementTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SubextensionCorrespondence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantCyclotomicExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basis

/-!
# Actual norm cofinality at prime-to-characteristic index

A finite constant extension supplies roots of unity. Pulling the open
subgroup back by its actual norm preserves openness and contains all
powers of the original index. An actual S-unit Kummer extension then
supplies a norm subgroup inside this inverse image. The norm tower and
the actual normal-closure abelian refinement return to the original base.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [IsSepClosure K Ω]

/-- Every ordinary open subgroup of finite prime-to-characteristic index
contains the actual norm image of a finite abelian subextension. -/
theorem exists_finiteAbelian_norm_le_of_primeToCharacteristic
    (H : Subgroup (IdeleClassGroup k K))
    (hH : IsOpen (H : Set (IdeleClassGroup k K)))
    [H.FiniteIndex] [NeZero (H.index : k)] :
    ∃ A : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K A ∧
      (have _ : HasPrincipalDivisors k A :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
      (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range ≤ H) := by
  have hHnormal : H.Normal := by
    constructor
    intro a ha g
    simpa only [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one] using ha
  let n : ℕ+ := ⟨H.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  have hclosed : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨C, hmu⟩ := exists_constantStage_primitiveRoot k K Ω H.index
  let K' := constantExtensionStage (K := K) C.toIntermediateField
  have hkK'Ω : IsScalarTower k K' Ω := IsScalarTower.to₁₃₄ k K K' Ω
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K K'
  let aR : Algebra (RatFunc k) K' := presentation.val
  have hkR : IsScalarTower k (RatFunc k) K' := presentation.property.1
  have hfunction : FunctionField k K' := presentation.property.2
  have hcurve : IsCurveOver k K' := isCurveOver k K'
  have hclosure : IsSepClosure K' Ω :=
    ⟨hclosed, Algebra.isSeparable_tower_top_of_isSeparable K K' Ω⟩
  have hn : ((n : ℕ) : K') ≠ 0 := by
    rw [← map_natCast (algebraMap k K')]
    exact (map_ne_zero (algebraMap k K')).mpr (NeZero.ne (H.index : k))
  let N : IdeleClassGroup k K' →* IdeleClassGroup k K :=
    IdeleClassGroup.norm (k := k) (K := K) (L := K')
  let H' : Subgroup (IdeleClassGroup k K') := H.comap N
  have hH' : IsOpen (H' : Set (IdeleClassGroup k K')) :=
    hH.preimage (IdeleClassGroup.continuous_norm (k := k) (K := K) (L := K'))
  obtain ⟨m, hm⟩ := RayClass.exists_rayClassSubgroup_le H' hH'
  have hpower : RayClass.powerRaySubgroup m (n : ℕ) ≤ H' := by
    apply sup_le hm
    rintro c ⟨d, rfl⟩
    change N (d ^ H.index) ∈ H
    rw [map_pow]
    exact H.pow_index_mem (N d)
  obtain ⟨E, hEabelian, hEnorm⟩ :=
    exists_finiteAbelian_norm_le_rayPower_of_roots k K' Ω m n hn hmu
  apply exists_finiteAbelian_norm_le_of_relative k K Ω K' H E
  intro hEprincipal
  exact hEnorm.trans hpower

/-- An ordinary open subgroup of finite prime-to-characteristic index is
exactly the norm group of an actual finite abelian class field. -/
theorem exists_classField_of_primeToCharacteristic
    (H : Subgroup (IdeleClassGroup k K))
    (hH : IsOpen (H : Set (IdeleClassGroup k K)))
    [H.FiniteIndex] [NeZero (H.index : k)] :
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
    ∃ (F : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K F)
      (_ : IsAbelianGalois K F),
      (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range = H := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  obtain ⟨A, hA, hAN⟩ :=
    exists_finiteAbelian_norm_le_of_primeToCharacteristic k K (SeparableClosure K) H hH
  have hAabelian : IsAbelianGalois K A := hA
  obtain ⟨F, hFfinite, hFabelian, hFA, hFnorm⟩ :=
    exists_subextension_norm_eq k K A.toIntermediateField H hAN
  exact ⟨F, hFfinite, hFabelian, hFnorm⟩

end FunctionField
