/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
import Nyll.ProCGroups.Topologies.DenseSubgroupPullback

/-!
# Inclusion and uniqueness of actual abelian class fields

The norm subgroup of an actual finite abelian extension determines that
extension uniquely inside the separable closure. Norm inclusion reverses
field inclusion, using density of absolute reciprocity and the actual
finite Galois correspondence.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every finite absolute quotient pulls back to the norm group of its actual fixed field. -/
theorem absoluteArtin_comap_openNormal
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
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
    N.toSubgroup.comap (absoluteArtin k K).toMonoidHom =
      (IdeleClassGroup.norm (k := k) (K := K) (L := absoluteFiniteQuotientField K N)).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  apply Subgroup.ext
  intro c
  change absoluteArtin k K c ∈ N ↔ _
  have hq := QuotientGroup.eq_one_iff (N := N.toSubgroup) (absoluteArtin k K c)
  have hc := absoluteFiniteArtinCoordinate_eq_one_iff_mem_norm k K N c
  rw [absoluteArtin_finiteProjection] at hq
  exact hq.symm.trans hc

/-- Pullback of a finite restriction kernel is the actual idele-class norm subgroup. -/
theorem absoluteArtin_comap_restrictionKernel
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
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
    (absoluteAbelianRestrictionKernel K E).toSubgroup.comap
        (absoluteArtin k K).toMonoidHom =
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  apply Subgroup.ext
  intro c
  change absoluteAbelianRestriction K E (absoluteArtin k K c) = 1 ↔ _
  rw [absoluteArtin_restriction]
  exact abelianFiniteArtin_eq_one_iff_mem_norm k K E c

/-- Inclusion of actual norm subgroups reverses inclusion of actual finite abelian fields. -/
theorem finiteAbelian_norm_range_le_iff
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [FiniteDimensional K F] [IsAbelianGalois K F] :
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
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ≤
      (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range ↔ F ≤ E := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  rw [← absoluteArtin_comap_restrictionKernel k K E,
    ← absoluteArtin_comap_restrictionKernel k K F]
  rw [ProCGroups.openSubgroup_comap_le_comap_iff
    (absoluteArtin k K).toMonoidHom (absoluteArtin_denseRange k K)
    (absoluteAbelianRestrictionKernel K E).toOpenSubgroup
    (absoluteAbelianRestrictionKernel K F).toOpenSubgroup]
  constructor
  · intro h
    have hi := absoluteFiniteQuotientField_antitone h
    rw [absoluteFiniteQuotientField_restrictionKernel,
      absoluteFiniteQuotientField_restrictionKernel] at hi
    exact hi
  · intro h x hx
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
    change absoluteAbelianRestriction K E (QuotientGroup.mk σ) = 1 at hx
    change absoluteAbelianRestriction K F (QuotientGroup.mk σ) = 1
    rw [absoluteAbelianRestriction_mk] at hx ⊢
    have hfix : σ ∈ E.fixingSubgroup := by
      rw [← E.restrictNormalHom_ker]
      exact hx
    have hfixF : σ ∈ F.fixingSubgroup := (IntermediateField.fixingSubgroup_le h) hfix
    rw [← F.restrictNormalHom_ker] at hfixF
    exact hfixF

/-- Two finite abelian subextensions with the same actual norm subgroup are equal. -/
theorem finiteAbelian_norm_range_eq_iff
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [FiniteDimensional K F] [IsAbelianGalois K F] :
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
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range =
      (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range ↔ E = F := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  constructor
  · intro h
    exact le_antisymm ((finiteAbelian_norm_range_le_iff k K F E).mp h.ge)
      ((finiteAbelian_norm_range_le_iff k K E F).mp h.le)
  · rintro rfl
    rfl

end FunctionField
