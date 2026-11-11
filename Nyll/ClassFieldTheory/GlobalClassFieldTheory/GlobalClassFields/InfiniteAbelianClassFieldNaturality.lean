/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr

/-!
# Naturality of the infinite abelian class-field correspondence

The specified maximal-field base equivalence transports the actual fixed field.
The subgroup square follows from equality of the Artin maps on each idèle class,
and the inverse square follows from the inverse laws of the same correspondence.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v w x

/-- Compatible field equivalences take the fixed field to the fixed field of
its actual conjugated subgroup, using the original image subfield. -/
theorem intermediateFieldMapRingEquiv_fixedField
    {K : Type u} {Ω : Type v} {M : Type w} {Ψ : Type x}
    [Field K] [Field Ω] [Field M] [Field Ψ] [Algebra K Ω] [Algebra M Ψ]
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (S : Subgroup Gal(Ω/K)) :
    intermediateFieldMapRingEquiv e c hc (IntermediateField.fixedField S) =
      IntermediateField.fixedField
        (S.map (semilinearGaloisEquiv e c hc).toMonoidHom) := by
  ext y
  change (∃ z, z ∈ IntermediateField.fixedField S ∧ c z = y) ↔ _
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    rintro σ ⟨τ, hτ, rfl⟩
    change c (τ (c.symm (c z))) = c z
    rw [c.symm_apply_apply, (IntermediateField.mem_fixedField_iff S z).mp hz τ hτ]
  · intro hy
    refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ hσ
    apply c.injective
    have h := (IntermediateField.mem_fixedField_iff _ y).mp hy
      (semilinearGaloisEquiv e c hc σ)
      (Subgroup.mem_map_of_mem (semilinearGaloisEquiv e c hc).toMonoidHom hσ)
    change c (σ (c.symm y)) = y at h
    exact h.trans (c.apply_symm_apply y).symm

end ClassFieldTheory

namespace GlobalClassFieldTheory.Reciprocity

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

/-- Native component-quotient reciprocity commutes with the specified base
and maximal-field equivalences on every quotient class. -/
theorem ideleClassComponentQuotientEquivMaximalAbelianGalois_baseEquiv
    (e : K ≃ₐ[ℚ] M) (z : ideleClassComponentQuotient K) :
    let q := ClassFieldTheory.connectedComponentQuotientCongr
      (ideleClassCongrContinuousMulEquiv e)
    let c := ClassFieldTheory.maximalAbelianExtensionBaseEquiv e.toRingEquiv
    let hc := ClassFieldTheory.maximalAbelianExtensionBaseEquiv_commutes e.toRingEquiv
    ideleClassComponentQuotientEquivMaximalAbelianGalois M (q z) =
      ClassFieldTheory.semilinearGaloisEquiv e.toRingEquiv c hc
        (ideleClassComponentQuotientEquivMaximalAbelianGalois K z) := by
  intro q c hc
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ideleClassIdentityComponent K) z
  change ideleClassComponentQuotientEquivMaximalAbelianGalois M
      (ClassFieldTheory.connectedComponentQuotientCongr
        (ideleClassCongrContinuousMulEquiv e)
        (QuotientGroup.mk'
          (Subgroup.connectedComponentOfOne (IdeleClassGroup K)) a)) = _
  rw [ClassFieldTheory.connectedComponentQuotientCongr_mk,
    ideleClassCongrContinuousMulEquiv_apply]
  change ideleClassComponentQuotientEquivMaximalAbelianGalois M
      (QuotientGroup.mk' (ideleClassIdentityComponent M) (ideleClassCongr e a)) = _
  rw [ideleClassComponentQuotientEquivMaximalAbelianGalois_mk,
    ideleClassComponentQuotientEquivMaximalAbelianGalois_mk]
  exact (infiniteGlobalIdeleClassArtinMonoidHom_semilinear e c hc a).symm

end GlobalClassFieldTheory.Reciprocity

namespace GlobalClassFieldTheory.GlobalClassFields

open Reciprocity

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

/-- The same infinite class field is transported by the actual maximal-field
base equivalence when the subgroup is transported on the idèle side. -/
theorem infiniteAbelianClassFieldCorrespondence_baseEquiv
    (e : K ≃ₐ[ℚ] M) (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    let q := ClassFieldTheory.connectedComponentQuotientCongr
      (ideleClassCongrContinuousMulEquiv e)
    let c := ClassFieldTheory.maximalAbelianExtensionBaseEquiv e.toRingEquiv
    let hc := ClassFieldTheory.maximalAbelianExtensionBaseEquiv_commutes e.toRingEquiv
    ClassFieldTheory.intermediateFieldMapRingEquiv e.toRingEquiv c hc
        (infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H)) =
      infiniteAbelianClassFieldCorrespondence M
        (OrderDual.toDual (ClosedSubgroup.mapContinuousMulEquiv q H)) := by
  intro q c hc
  simp only [infiniteAbelianClassFieldCorrespondence_apply]
  rw [ClassFieldTheory.intermediateFieldMapRingEquiv_fixedField]
  apply congrArg IntermediateField.fixedField
  change
    (H.toSubgroup.map
      (ideleClassComponentQuotientEquivMaximalAbelianGalois K).toMonoidHom).map
        (ClassFieldTheory.semilinearGaloisEquiv e.toRingEquiv c hc).toMonoidHom =
      (H.toSubgroup.map q.toMonoidHom).map
        (ideleClassComponentQuotientEquivMaximalAbelianGalois M).toMonoidHom
  let fK := (ideleClassComponentQuotientEquivMaximalAbelianGalois K).toMonoidHom
  let fM := (ideleClassComponentQuotientEquivMaximalAbelianGalois M).toMonoidHom
  let t := (ClassFieldTheory.semilinearGaloisEquiv e.toRingEquiv c hc).toMonoidHom
  have h : t.comp fK = fM.comp q.toMonoidHom :=
    MonoidHom.ext fun z => (ideleClassComponentQuotientEquivMaximalAbelianGalois_baseEquiv e z).symm
  exact (Subgroup.map_map H.toSubgroup t fK).trans
    ((congrArg (fun f => H.toSubgroup.map f) h).trans
      (Subgroup.map_map H.toSubgroup fM q.toMonoidHom).symm)

/-- The inverse of the same infinite correspondence satisfies the reverse
base-equivalence square, by the actual forward square and both inverse laws. -/
theorem infiniteAbelianClassFieldCorrespondence_symm_baseEquiv
    (e : K ≃ₐ[ℚ] M) (L : IntermediateField K (maximalAbelianExtension K)) :
    let q := ClassFieldTheory.connectedComponentQuotientCongr
      (ideleClassCongrContinuousMulEquiv e)
    let c := ClassFieldTheory.maximalAbelianExtensionBaseEquiv e.toRingEquiv
    let hc := ClassFieldTheory.maximalAbelianExtensionBaseEquiv_commutes e.toRingEquiv
    (infiniteAbelianClassFieldCorrespondence M).symm
        (ClassFieldTheory.intermediateFieldMapRingEquiv e.toRingEquiv c hc L) =
      OrderDual.toDual (ClosedSubgroup.mapContinuousMulEquiv q
        (OrderDual.ofDual ((infiniteAbelianClassFieldCorrespondence K).symm L))) := by
  intro q c hc
  apply (infiniteAbelianClassFieldCorrespondence M).injective
  rw [(infiniteAbelianClassFieldCorrespondence M).apply_symm_apply]
  have h := infiniteAbelianClassFieldCorrespondence_baseEquiv e
    (OrderDual.ofDual ((infiniteAbelianClassFieldCorrespondence K).symm L))
  change ClassFieldTheory.intermediateFieldMapRingEquiv e.toRingEquiv c hc
      (infiniteAbelianClassFieldCorrespondence K
        ((infiniteAbelianClassFieldCorrespondence K).symm L)) = _ at h
  rw [(infiniteAbelianClassFieldCorrespondence K).apply_symm_apply] at h
  exact h

end GlobalClassFieldTheory.GlobalClassFields
