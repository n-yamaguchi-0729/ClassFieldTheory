/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel

/-!
# Infinite abelian class-field correspondence

Maximal abelian reciprocity transports closed subgroups of the idele-class
component quotient to closed subgroups of the maximal abelian Galois group.
Composing this transport with the infinite Galois correspondence gives the
order-reversing infinite abelian class-field correspondence.
-/


@[expose] public section

open scoped NumberField

noncomputable section


namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The infinite abelian class-field correspondence.  The order dual in the
domain records that larger closed idele-class subgroups correspond to smaller
intermediate fields. -/
noncomputable def infiniteAbelianClassFieldCorrespondence :
    (ClosedSubgroup (ideleClassComponentQuotient K))ᵒᵈ ≃o
      IntermediateField K (maximalAbelianExtension K) :=
  (ClosedSubgroup.orderDualIsoMapContinuousMulEquiv
      (ideleClassComponentQuotientEquivMaximalAbelianGalois K)).trans
    (InfiniteGalois.IntermediateFieldEquivClosedSubgroup
      (k := K) (K := maximalAbelianExtension K)).symm

/-- Forward evaluation is the fixed field of the transported closed
idele-class subgroup. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_apply
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H) =
      IntermediateField.fixedField
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K) H) :=
  rfl

/-- The inverse correspondence is the fixing subgroup transported back to
the idele-class component quotient. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_symm_apply
    (L : IntermediateField K (maximalAbelianExtension K)) :
    (infiniteAbelianClassFieldCorrespondence K).symm L =
      OrderDual.toDual
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K).symm
          { toSubgroup := L.fixingSubgroup
            isClosed' := InfiniteGalois.fixingSubgroup_isClosed L }) :=
  rfl

/-- The fixing subgroup of the field corresponding to `H` is exactly the
transport of `H` by maximal abelian reciprocity. -/
theorem infiniteAbelianClassFieldCorrespondence_fixingSubgroup
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    (infiniteAbelianClassFieldCorrespondence K
        (OrderDual.toDual H)).fixingSubgroup =
      (ClosedSubgroup.mapContinuousMulEquiv
        (ideleClassComponentQuotientEquivMaximalAbelianGalois K) H).toSubgroup := by
  rw [infiniteAbelianClassFieldCorrespondence_apply]
  exact InfiniteGalois.fixingSubgroup_fixedField _

/-- A field in the infinite abelian correspondence is finite over the base
exactly when the corresponding closed idele-class subgroup is open. -/
theorem infiniteAbelianClassFieldCorrespondence_finite_iff_open
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    FiniteDimensional K
        (infiniteAbelianClassFieldCorrespondence K
          (OrderDual.toDual H)) ↔
      IsOpen (H : Set (ideleClassComponentQuotient K)) := by
  let L :=
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H)
  let e := ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let T := ClosedSubgroup.mapContinuousMulEquiv e H
  have hfix : L.fixingSubgroup = T.toSubgroup := by
    simpa only [L, T, e] using
      infiniteAbelianClassFieldCorrespondence_fixingSubgroup K H
  calc
    FiniteDimensional K L ↔
        IsOpen (L.fixingSubgroup : Set
          Gal(maximalAbelianExtension K / K)) :=
      (InfiniteGalois.isOpen_iff_finite L).symm
    _ ↔ IsOpen (T : Set Gal(maximalAbelianExtension K / K)) := by
      rw [hfix]
      change
        IsOpen (T : Set Gal(maximalAbelianExtension K / K)) ↔
          IsOpen (T : Set Gal(maximalAbelianExtension K / K))
      exact Iff.rfl
    _ ↔ IsOpen (H : Set (ideleClassComponentQuotient K)) := by
      change
        IsOpen (e '' (H : Set (ideleClassComponentQuotient K))) ↔
          IsOpen (H : Set (ideleClassComponentQuotient K))
      exact e.toHomeomorph.isOpen_image


/-- Pulling the fixing subgroup of a finite layer back along the actual
maximal-abelian Artin map gives the ordinary idèle-class norm range. -/
theorem maximalAbelianGlobalArtin_comap_fixingSubgroup
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    let : NumberField E := NumberField.of_module_finite K E
    E.toIntermediateField.fixingSubgroup.comap
        (maximalAbelianGlobalArtin K).toMonoidHom =
      (_root_.ideleClassNorm K E).range := by
  intro numberFieldE
  ext c
  obtain ⟨a, rfl⟩ := IdeleGroup.toStandardClass_surjective K c
  let q := IdeleGroup.toStandardClass K a
  let g := maximalAbelianGlobalArtin K q
  change g ∈ E.toIntermediateField.fixingSubgroup ↔ q ∈ (_root_.ideleClassNorm K E).range
  have hfix : g ∈ E.toIntermediateField.fixingSubgroup ↔ AlgEquiv.restrictNormalHom E g = 1 := by
    rw [← E.toIntermediateField.restrictNormalHom_ker]
    exact Iff.rfl
  have hproj : AlgEquiv.restrictNormalHom E g =
      globalNormResidueMonoidHom K E q :=
    (maximalAbelianGlobalArtin_finiteProjection K a E).trans
      (globalNormResidueMonoidHom_mk (K := K) (L := E) a).symm
  exact hfix.trans ((congrArg (· = 1) hproj).to_iff.trans
    (globalNormResidueMonoidHom_eq_one_iff (K := K) (L := E) q))

/-- The infinite correspondence recovers the original subgroup on idèle
classes, through the same component quotient and the same Artin map. -/
theorem infiniteAbelianClassFieldCorrespondence_comap_fixingSubgroup
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    (infiniteAbelianClassFieldCorrespondence K
        (OrderDual.toDual H)).fixingSubgroup.comap
        (maximalAbelianGlobalArtin K).toMonoidHom =
      H.toSubgroup.comap (QuotientGroup.mk' (ideleClassIdentityComponent K)) := by
  rw [infiniteAbelianClassFieldCorrespondence_fixingSubgroup]
  ext c
  change maximalAbelianGlobalArtin K c ∈
      H.toSubgroup.map
        (ideleClassComponentQuotientEquivMaximalAbelianGalois K).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  rw [← ideleClassComponentQuotientEquivMaximalAbelianGalois_mk K c]
  let e := (ideleClassComponentQuotientEquivMaximalAbelianGalois K).toMulEquiv
  let q := QuotientGroup.mk' (ideleClassIdentityComponent K) c
  change e.symm (e q) ∈ H.toSubgroup ↔ q ∈ H.toSubgroup
  rw [e.symm_apply_apply]

/-- On finite layers, the infinite correspondence is characterized by the
actual ordinary norm range. This identifies fields inside the same maximal
abelian extension, not just isomorphic abstract fields. -/
theorem infiniteAbelianClassFieldCorrespondence_eq_finiteLayer_iff
    (H : ClosedSubgroup (ideleClassComponentQuotient K))
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    let : NumberField E := NumberField.of_module_finite K E
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H) =
        E.toIntermediateField ↔
      H.toSubgroup.comap (QuotientGroup.mk' (ideleClassIdentityComponent K)) =
        (_root_.ideleClassNorm K E).range := by
  intro numberFieldE
  constructor
  · intro h
    calc
      H.toSubgroup.comap (QuotientGroup.mk' (ideleClassIdentityComponent K)) =
          (infiniteAbelianClassFieldCorrespondence K
            (OrderDual.toDual H)).fixingSubgroup.comap
            (maximalAbelianGlobalArtin K).toMonoidHom :=
        (infiniteAbelianClassFieldCorrespondence_comap_fixingSubgroup K H).symm
      _ = E.toIntermediateField.fixingSubgroup.comap
          (maximalAbelianGlobalArtin K).toMonoidHom := by rw [h]
      _ = (_root_.ideleClassNorm K E).range :=
        maximalAbelianGlobalArtin_comap_fixingSubgroup K E
  · intro h
    have hfix :
        (infiniteAbelianClassFieldCorrespondence K
          (OrderDual.toDual H)).fixingSubgroup = E.toIntermediateField.fixingSubgroup := by
      apply Subgroup.comap_injective (maximalAbelianGlobalArtin_surjective K)
      exact (infiniteAbelianClassFieldCorrespondence_comap_fixingSubgroup K H).trans
        (h.trans (maximalAbelianGlobalArtin_comap_fixingSubgroup K E).symm)
    have hfield := congrArg IntermediateField.fixedField hfix
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using hfield

/-- The finite/open part of infinite reciprocity is the existing selected
finite class field embedded by its specified embedding into the maximal
abelian extension. No new class-field choice is introduced. -/
theorem infiniteAbelianClassFieldCorrespondence_eq_closedFiniteIndexClassField
    (H : ClosedSubgroup (ideleClassComponentQuotient K))
    [(H.toSubgroup.comap
      (QuotientGroup.mk' (ideleClassIdentityComponent K))).FiniteIndex] :
    let P := H.toSubgroup.comap (QuotientGroup.mk' (ideleClassIdentityComponent K))
    let hP : IsClosed (P : Set (IdeleClassGroup K)) :=
      H.isClosed'.preimage QuotientGroup.continuous_mk
    let L := closedFiniteIndexClassField (K := K) P hP
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H) =
      (finiteAbelianExtensionInMaximalAbelianExtension K L).toIntermediateField := by
  intro P hP L
  let : NumberField L := NumberField.of_module_finite K L
  let E := finiteAbelianExtensionInMaximalAbelianExtension K L
  let : NumberField E := NumberField.of_module_finite K E
  apply (infiniteAbelianClassFieldCorrespondence_eq_finiteLayer_iff K H E).2
  change P = (_root_.ideleClassNorm K E).range
  exact ((finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range K L).trans
    (closedFiniteIndexClassField_ideleClassNorm_range (K := K) P hP)).symm

end GlobalClassFields
end GlobalClassFieldTheory
