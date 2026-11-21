/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Nyll.ClassFieldTheory.Algebra.LocalField.PrincipalUnitTopology
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFiltered
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocity
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.Ramification.LocalField.AbsoluteUpper
public import Nyll.ValuedFieldTheory.Ramification.LocalField.ResidueInertia

/-!
# Absolute filtered local reciprocity

The actual image of a principal-unit subgroup is the image of the absolute
upper group in the topological abelianization. Both images are compact, and
their finite quotient images agree by finite filtered reciprocity and Herbrand
quotient compatibility.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField ProCGroups.Abelian
open RamificationTheory.LocalField

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- In the separable-closure abelianization, actual Artin carries the principal
units at the real step `⌈t⌉₊` onto the image of the absolute upper group at `t`. -/
theorem separableAbsoluteLocalArtinMap_fieldPrincipalUnits (t : ℝ) (ht : 0 ≤ t) :
    (fieldPrincipalUnits K ⌈t⌉₊).map (separableAbsoluteLocalArtinMap K).toMonoidHom =
      (separableLocalUpperRamificationGroup K t).map
        (localAbsoluteAbelianizationQuotientMap K) := by
  let U := fieldPrincipalUnits K ⌈t⌉₊
  let W := separableLocalUpperRamificationGroup K t
  let artin := separableAbsoluteLocalArtinMap K
  let ab := localAbsoluteAbelianizationQuotientMap K
  let I := U.map artin.toMonoidHom
  let R := W.map ab
  have hI : IsClosed (I : Set (localAbsoluteAbelianProfinite K)) :=
    ((isCompact_fieldPrincipalUnits K ⌈t⌉₊).image artin.continuous).isClosed
  have hab : Continuous ab := QuotientGroup.continuous_mk
  have hR : IsClosed (R : Set (localAbsoluteAbelianProfinite K)) :=
    (((separableLocalUpperRamificationGroup_isClosed K t).isCompact).image hab).isClosed
  have hquotient (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
      I.map (QuotientGroup.mk' N.toSubgroup) = R.map (QuotientGroup.mk' N.toSubgroup) := by
    let E := absoluteFiniteQuotientField K N
    let F : FiniteGaloisIntermediateField K (SeparableClosure K) := { toIntermediateField := E }
    let e := absoluteFiniteQuotientEquiv K N
    let q := QuotientGroup.mk' N.toSubgroup
    have hArtin : (e.toMulEquiv.toMonoidHom.comp q).comp artin.toMonoidHom =
        abelianLocalArtinMonoidHom K E := by
      rw [← abelianLocalArtinMap_toMonoidHom K E]
      apply MonoidHom.ext
      intro a
      change e (QuotientGroup.mk' N.toSubgroup (separableAbsoluteLocalArtinMap K a)) =
        abelianLocalArtinMap K E a
      rw [separableAbsoluteLocalArtinMap_finiteProjection]
      exact e.apply_symm_apply _
    have hAb : (e.toMulEquiv.toMonoidHom.comp q).comp ab =
        AlgEquiv.restrictNormalHom E := by
      apply MonoidHom.ext
      intro σ
      exact absoluteFiniteQuotientEquiv_mk_mk K N σ
    have hW : W.map (AlgEquiv.restrictNormalHom E) = localUpperRamificationGroup K E t :=
      separableLocalUpperRamificationGroup_map_restrict K t F
    apply Subgroup.map_injective (f := e.toMulEquiv.toMonoidHom) e.injective
    change ((U.map artin.toMonoidHom).map q).map e.toMulEquiv.toMonoidHom =
      ((W.map ab).map q).map e.toMulEquiv.toMonoidHom
    simp only [Subgroup.map_map, ← MonoidHom.comp_assoc, hArtin, hAb, hW]
    exact Universe.finiteAbelian_filteredLocalReciprocity K E t ht
  change I = R
  ext x
  change (x ∈ (I : Set (localAbsoluteAbelianProfinite K))) ↔
    x ∈ (R : Set (localAbsoluteAbelianProfinite K))
  rw [ProCGroups.mem_closed_iff_forall_openNormal_quotient hI,
    ProCGroups.mem_closed_iff_forall_openNormal_quotient hR]
  constructor
  · intro h N
    change QuotientGroup.mk' N.toSubgroup x ∈ R.map (QuotientGroup.mk' N.toSubgroup)
    rw [← hquotient]
    exact h N
  · intro h N
    change QuotientGroup.mk' N.toSubgroup x ∈ I.map (QuotientGroup.mk' N.toSubgroup)
    rw [hquotient]
    exact h N

/-- The usual absolute Artin map has the same upper-group image, transported
by the canonical comparison of the separable and standard abelianizations. -/
theorem absoluteLocalArtinMap_fieldPrincipalUnits (t : ℝ) (ht : 0 ≤ t) :
    (fieldPrincipalUnits K ⌈t⌉₊).map (absoluteLocalArtinMap K).toMonoidHom =
      ((separableLocalUpperRamificationGroup K t).map
        (localAbsoluteAbelianizationQuotientMap K)).map
          (separableToStandardAbsoluteAbelianizationHom K).toMonoidHom := by
  change (fieldPrincipalUnits K ⌈t⌉₊).map
      ((separableToStandardAbsoluteAbelianizationHom K).toMonoidHom.comp
        (separableAbsoluteLocalArtinMap K).toMonoidHom) = _
  rw [← Subgroup.map_map, separableAbsoluteLocalArtinMap_fieldPrincipalUnits K t ht]

/-- At integral depth the absolute upper group has the image of the ordinary
principal-unit step of that depth. -/
theorem separableAbsoluteLocalArtinMap_fieldPrincipalUnits_nat (n : ℕ) :
    (fieldPrincipalUnits K n).map (separableAbsoluteLocalArtinMap K).toMonoidHom =
      (separableLocalUpperRamificationGroup K (n : ℝ)).map
        (localAbsoluteAbelianizationQuotientMap K) := by
  simpa only [Nat.ceil_natCast] using
    separableAbsoluteLocalArtinMap_fieldPrincipalUnits K (n : ℝ) (Nat.cast_nonneg n)

/-- The image of the zeroth absolute upper group is also the image of the
kernel of the actual absolute residue degree. -/
theorem separableLocalUpperRamificationGroup_zero_map_abelianization :
    (separableLocalUpperRamificationGroup K 0).map (localAbsoluteAbelianizationQuotientMap K) =
      (localResidueDegree K).toMonoidHom.ker.map (localAbsoluteAbelianizationQuotientMap K) := by
  rw [← separableAbsoluteLocalArtinMap_fieldPrincipalUnits K 0 le_rfl, Nat.ceil_zero]
  let degree := localAbsoluteAbelianResidueDegree K
  let ab := localAbsoluteAbelianizationQuotientMap K
  have hInertia : (localResidueDegree K).toMonoidHom.ker.map ab = degree.toMonoidHom.ker := by
    ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro ha
      obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure K / K) a
      exact ⟨g, ha, rfl⟩
  change (fieldPrincipalUnits K 0).map (separableAbsoluteLocalArtinMap K).toMonoidHom =
    (localResidueDegree K).toMonoidHom.ker.map ab
  rw [hInertia]
  ext a
  constructor
  · rintro ⟨x, ⟨u, _hu, rfl⟩, rfl⟩
    change degree (separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u)) = 1
    rw [localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap K]
    change localWeilIntegerInclusion
      (Multiplicative.ofAdd (valuationMap K (Additive.ofMul (integerUnitsToFieldUnits K u)))) = 1
    rw [valuationMap_apply, v_integerUnitsToFieldUnits]
    change localWeilIntegerInclusion 1 = 1
    exact map_one localWeilIntegerInclusion
  · intro ha
    obtain ⟨u, hu⟩ := exists_unit_separableAbsoluteLocalArtinMap_of_degree_one K a ha
    refine ⟨integerUnitsToFieldUnits K u, ⟨u, ?_, rfl⟩, hu⟩
    rw [principalUnits_zero]
    exact Subgroup.mem_top u

/-- The zeroth upper group in the separable Galois group is actual inertia. -/
theorem separableLocalUpperRamificationGroup_zero_eq_ker_residueDegree :
    separableLocalUpperRamificationGroup K 0 = (localResidueDegree K).toMonoidHom.ker := by
  let ab := localAbsoluteAbelianizationQuotientMap K
  let W := separableLocalUpperRamificationGroup K 0
  let I := (localResidueDegree K).toMonoidHom.ker
  have hab : ab.ker = (commutator Gal(SeparableClosure K/K)).topologicalClosure :=
    QuotientGroup.ker_mk' _
  have hW : ab.ker ≤ W := by
    rw [hab]
    apply Subgroup.topologicalClosure_minimal _ ?_
      (separableLocalUpperRamificationGroup_isClosed K 0)
    intro σ hσ
    apply (mem_separableLocalUpperRamificationGroup_iff K 0 σ).mpr
    intro F
    let r : Gal(SeparableClosure K/K) →* Gal(F/K) :=
      AlgEquiv.restrictNormalHom F.toIntermediateField
    have hmap : σ ∈ (localUpperRamificationGroup K F 0).comap r := by
      let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
      let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
      let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
      let : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        finiteExtensionSpectralValuation_hasExtension K F
      let : IsIntegralClosure 𝒪[F] 𝒪[K] F := localCompleteDVF_integerRing_isIntegralClosure K F
      let : Module.Finite 𝒪[K] 𝒪[F] := localCompleteDVF_integerRing_moduleFinite K F
      let residue := galoisGroupResidueAlgEquivHomOfIsIntegralClosure K F
      let : IsMulCommutative Gal(𝓀[F]/𝓀[K]) := inferInstance
      rw [localUpperRamificationGroup_zero_eq_residue_ker K F]
      exact Group.Abelianization.commutator_le_ker (residue.comp r) hσ
    exact hmap
  have hI : ab.ker ≤ I := by
    rw [hab]
    exact Subgroup.topologicalClosure_minimal _
      (Group.Abelianization.commutator_le_ker (localResidueDegree K).toMonoidHom)
      (isClosed_singleton.preimage (localResidueDegree K).continuous)
  exact Subgroup.map_injective_of_ker_le ab hW hI
    (separableLocalUpperRamificationGroup_zero_map_abelianization K)

end LocalClassFieldTheory
