/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelianNative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Filtered reciprocity for finite Galois extensions

The commutator fixed field computes both the Artin symbol and the upper
ramification group in the abelianization of a finite Galois group.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel IsMulCommutative

namespace LocalClassFieldTheory

open LocalFieldTheory ProCGroups.Abelian RamificationTheory.LocalField

variable (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]

/-- For any finite Galois extension, the image of the `⌈t⌉₊` principal units
under the actual finite Artin symbol is the image of its upper group in the
algebraic Galois abelianization. -/
theorem finiteGalois_filteredLocalReciprocity_algebraic (t : ℝ) (ht : 0 ≤ t) :
    (fieldPrincipalUnits K ⌈t⌉₊).map (localArtinMonoidHom K L) =
      (localUpperRamificationGroup K L t).map Group.Abelianization.of := by
  let H := commutator Gal(L/K)
  let A := IntermediateField.fixedField H
  let : IsGalois K A := IsGalois.of_fixedField_normal_subgroup H
  let e : Group.Abelianization Gal(L/K) ≃* Gal(A/K) := IsGalois.normalAutEquivQuotient H
  let : IsAbelianGalois K A :=
    { toIsGalois := inferInstance
      toIsMulCommutative := e.surjective.isMulCommutative }
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A
  have he (σ : Gal(L/K)) : e (Group.Abelianization.of σ) = r σ :=
    IsGalois.normalAutEquivQuotient_apply H σ
  have hUpper : e.toMonoidHom.comp Group.Abelianization.of = r := by
    apply MonoidHom.ext
    exact he
  have hArtin (a : Kˣ) : e (localArtinMonoidHom K L a) = abelianLocalArtinMonoidHom K A a := by
    have h (z : Group.Abelianization Gal(L/K)) :
        Group.Abelianization.of (e z) = Group.Abelianization.map r z := by
      refine QuotientGroup.induction_on z ?_
      intro σ
      change Group.Abelianization.of (e (Group.Abelianization.of σ)) =
        Group.Abelianization.map r (Group.Abelianization.of σ)
      rw [he, Group.Abelianization.map_of]
    apply (Group.Abelianization.equivOfComm (H := Gal(A/K))).injective
    change Group.Abelianization.of (e (localArtinMonoidHom K L a)) =
      Group.Abelianization.of (abelianLocalArtinMonoidHom K A a)
    rw [h, localArtinMonoidHom_restrict_tower K A L]
    exact ((Group.Abelianization.equivOfComm (H := Gal(A/K))).apply_symm_apply _).symm
  have hArtinHom : e.toMonoidHom.comp (localArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K A := by
    apply MonoidHom.ext
    exact hArtin
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_map, Subgroup.map_map, hUpper, hArtinHom,
    localUpperRamificationGroup_map_fixedField K L H t]
  rw [← artinPrincipalUnitStepGroup_eq_nativeArtinImage]
  exact finiteAbelian_filteredLocalReciprocity K A t ht

/-- The continuous finite Artin map has the same upper-group image in the
topological abelianization. -/
theorem finiteGalois_filteredLocalReciprocity (t : ℝ) (ht : 0 ≤ t) :
    (fieldPrincipalUnits K ⌈t⌉₊).map (localArtinMap K L).toMonoidHom =
      (localUpperRamificationGroup K L t).map (TopologicalAbelianization.mk Gal(L/K)) := by
  let e := topologicalAbelianization_finite_equiv K L
  have hquot : e.symm.toMonoidHom.comp (TopologicalAbelianization.mk Gal(L/K)) =
      Group.Abelianization.of := by
    apply MonoidHom.ext
    intro σ
    apply e.injective
    have hmk : e (Group.Abelianization.of σ) = TopologicalAbelianization.mk Gal(L/K) σ :=
      QuotientGroup.quotientMulEquivOfEq_mk _ _
    exact (e.apply_symm_apply (TopologicalAbelianization.mk Gal(L/K) σ)).trans hmk.symm
  apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
  rw [Subgroup.map_map, Subgroup.map_map, hquot]
  change (fieldPrincipalUnits K ⌈t⌉₊).map
      ((topologicalAbelianization_finite_equiv K L).symm.toMonoidHom.comp
        (localArtinMap K L).toMonoidHom) = _
  rw [localArtinMap_toMonoidHom]
  exact finiteGalois_filteredLocalReciprocity_algebraic K L t ht

end LocalClassFieldTheory
