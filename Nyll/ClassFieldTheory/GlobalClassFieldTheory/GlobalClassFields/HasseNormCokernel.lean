/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HasseNormObstruction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.PrincipalSequence

/-!
# The Galois norm obstruction as a Tate cokernel

For finite Galois extensions the same principal-idèle connecting map gives
the cokernel of `H⁻¹(G,I_L) → H⁻¹(G,C_L)` as the kernel of the actual norm
diagonal. This uses both adjacent exactness statements of the existing Tate
long exact sequence. The Tate representation comparison currently uses
fields in `Type`; the noncohomological norm obstruction has no such limit.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

open scoped NumberField
open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open RelativeIdeleGroup.Cohomology

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

attribute [local instance] RelativeIdeleGroup.relativeIdeleMulDistribMulAction
  principalIdeleMulDistribMulAction ideleClassMulDistribMulAction
  LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Exactness immediately before the existing principal-idèle connecting
map, with the actual quotient `I_L → C_L` as its preceding arrow. -/
theorem ideleClassToPrincipalConnecting_ker :
    (ideleClassToPrincipalConnecting K L).ker = (ideleToClassTateMinusOne K L).range := by
  let S := principalIdeleShortComplex K L
  have hS : S.ShortExact := principalIdeleShortComplex_shortExact K L
  let f := ideleToClassTateMinusOne K L
  let δm := (TateCohomology.δ hS (-1)).hom.toAddMonoidHom.toMultiplicative
  let eP₀ := tateH0IsoHerbrandH0 (G := L ≃ₐ[K] L)
    (A := RelativeIdeleGroup.principalSubgroup K L)
  let eP := eP₀.toLinearEquiv.toAddEquiv.toMultiplicative
  have hbase : Function.MulExact f δm := by
    apply mulExact_of_moduleCat_shortComplex_exact
    exact TateCohomology.exact₃ hS (-1)
  ext c
  change eP (δm c) = 1 ↔ c ∈ f.range
  constructor
  · intro hc
    exact (hbase c).mp (eP.injective (hc.trans eP.map_one.symm))
  · intro hc
    exact (congrArg eP ((hbase c).mpr hc)).trans eP.map_one

/-- A field-unit Tate class dies in idèle cohomology exactly when its
descended unit is an actual relative idèle norm. -/
theorem fieldUnitsToRelativeIdeleHerbrandH0_mk_eq_one_iff
    (a : fixedSubgroup (L ≃ₐ[K] L) Lˣ) :
    fieldUnitsToRelativeIdeleHerbrandH0 K L (HerbrandH0.mk a) = 1 ↔
      IdeleGroup.principalIdele K (CyclicCohomology.fixedUnitsEquivBaseUnits K L a) ∈
        (RelativeIdeleGroup.norm K L).range := by
  let aP := CyclicCohomology.fixedSubgroupEquivariantMulEquiv
    (fieldUnitsEquivPrincipalIdeles K L) (fieldUnitsEquivPrincipalIdeles_smul K L) a
  let aI : fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    ⟨(RelativeIdeleGroup.principalSubgroup K L).subtype aP, fun σ => by
      rw [← principalIdeleSubtype_equivariant K L σ aP, aP.2 σ]⟩
  have hmap : fieldUnitsToRelativeIdeleHerbrandH0 K L (HerbrandH0.mk a) =
      HerbrandH0.mk aI := by
    have hfield : fieldUnitsHerbrandH0EquivPrincipalIdeles K L (HerbrandH0.mk a) =
        HerbrandH0.mk aP :=
      CyclicCohomology.herbrandH0EquivariantMulEquiv_mk
        (fieldUnitsEquivPrincipalIdeles K L) (fieldUnitsEquivPrincipalIdeles_smul K L) a
    change principalIdeleHerbrandH0Map K L
      (fieldUnitsHerbrandH0EquivPrincipalIdeles K L (HerbrandH0.mk a)) = _
    rw [hfield]
    exact principalIdeleHerbrandH0Map_mk K L aP
  have hfixed : (aI : RelativeIdeleGroup K L) = RelativeIdeleGroup.inclusion K L
      (IdeleGroup.principalIdele K (CyclicCohomology.fixedUnitsEquivBaseUnits K L a)) := by
    rw [RelativeIdeleGroup.inclusion_principalIdele]
    change RelativeIdeleGroup.principalIdele K L (a : Lˣ) =
      RelativeIdeleGroup.principalIdele K L
        (Units.map (algebraMap K L) (CyclicCohomology.fixedUnitsEquivBaseUnits K L a))
    apply congrArg (RelativeIdeleGroup.principalIdele K L)
    apply Units.ext
    exact (CyclicCohomology.fixedUnitsEquivBaseUnits_spec K L a).symm
  rw [hmap, HerbrandH0.mk_eq_one_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, RelativeIdeleGroup.inclusion_injective K L ?_⟩
    rw [← relativeIdele_tateNorm_eq_inclusion_norm K L]
    exact hz.trans hfixed
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact (relativeIdele_tateNorm_eq_inclusion_norm K L z).trans
      ((congrArg (RelativeIdeleGroup.inclusion K L) hz).trans hfixed.symm)

/-- The norm-quotient comparison identifies the two actual kernels. -/
theorem hasseNormDiagonal_fieldUnitsEquiv_eq_one_iff
    (q : HerbrandH0 (L ≃ₐ[K] L) Lˣ) :
    NumberField.NormObstruction.hasseNormDiagonal K L
        (fieldUnitsHerbrandH0EquivGlobalNormQuotient K L q) = 1 ↔
      fieldUnitsToRelativeIdeleHerbrandH0 K L q = 1 := by
  obtain ⟨a, rfl⟩ := HerbrandH0.mk_surjective q
  have hmk : fieldUnitsHerbrandH0EquivGlobalNormQuotient K L (HerbrandH0.mk a) =
      QuotientGroup.mk' (localNormSubgroup K L)
        (CyclicCohomology.fixedUnitsEquivBaseUnits K L a) := rfl
  rw [hmk, NumberField.NormObstruction.hasseNormDiagonal_mk]
  change (((QuotientGroup.mk ((IdeleGroup.principalIdele K)
    (CyclicCohomology.fixedUnitsEquivBaseUnits K L a))) :
      _ ⧸ (IdeleGroup.norm K L).range) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff, ideleNorm_range_eq_allPlaceLocalNormCondition K L,
    ← relativeIdeleNorm_range_eq_allPlaceLocalNormCondition (K := K) (L := L)]
  exact (fieldUnitsToRelativeIdeleHerbrandH0_mk_eq_one_iff K L a).symm

/-- The existing connecting map, transported to the actual field norm
quotient by the established fixed-unit descent. -/
noncomputable def normObstructionConnecting :
    Multiplicative (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L)) (-1)) →*
      Kˣ ⧸ localNormSubgroup K L :=
  (fieldUnitsHerbrandH0EquivGlobalNormQuotient K L).toMonoidHom.comp
    (ideleClassToFieldUnitsConnecting K L)

/-- The image of the same connecting map is the actual knot subgroup. -/
theorem normObstructionConnecting_range :
    (normObstructionConnecting K L).range = NumberField.NormObstruction.Knot K L := by
  let e := fieldUnitsHerbrandH0EquivGlobalNormQuotient K L
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    apply (hasseNormDiagonal_fieldUnitsEquiv_eq_one_iff K L _).mpr
    exact (ideleClassToFieldUnitsConnecting_range_eq_ker K L).le ⟨c, rfl⟩
  · intro hq
    have hker : fieldUnitsToRelativeIdeleHerbrandH0 K L (e.symm q) = 1 := by
      apply (hasseNormDiagonal_fieldUnitsEquiv_eq_one_iff K L _).mp
      have hd := congrArg (NumberField.NormObstruction.hasseNormDiagonal K L)
        (e.apply_symm_apply q)
      exact hd.trans hq
    obtain ⟨c, hc⟩ := (ideleClassToFieldUnitsConnecting_range_eq_ker K L).ge hker
    refine ⟨c, ?_⟩
    change e (ideleClassToFieldUnitsConnecting K L c) = q
    exact (congrArg e hc).trans (e.apply_symm_apply q)

/-- Transport by the two field-unit equivalences preserves the preceding
exactness statement. -/
theorem normObstructionConnecting_ker :
    (normObstructionConnecting K L).ker = (ideleToClassTateMinusOne K L).range := by
  ext c
  change (fieldUnitsHerbrandH0EquivGlobalNormQuotient K L)
      ((fieldUnitsHerbrandH0EquivPrincipalIdeles K L).symm
        (ideleClassToPrincipalConnecting K L c)) = 1 ↔
    c ∈ (ideleToClassTateMinusOne K L).range
  rw [(fieldUnitsHerbrandH0EquivGlobalNormQuotient K L).map_eq_one_iff,
    (fieldUnitsHerbrandH0EquivPrincipalIdeles K L).symm.map_eq_one_iff]
  exact SetLike.ext_iff.mp (ideleClassToPrincipalConnecting_ker K L) c

/-- The Galois knot group is the cokernel of the actual map on
degree-minus-one Tate cohomology induced by `I_L → C_L`. -/
noncomputable def normObstructionCokernelEquivKnot :
    (Multiplicative (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L)) (-1)) ⧸
        (ideleToClassTateMinusOne K L).range) ≃* NumberField.NormObstruction.Knot K L :=
  (QuotientGroup.quotientMulEquivOfEq (normObstructionConnecting_ker K L).symm).trans
    ((QuotientGroup.quotientKerEquivRange (normObstructionConnecting K L)).trans
      (MulEquiv.subgroupCongr (normObstructionConnecting_range K L)))

/-- On a Tate class the cokernel comparison is exactly the original
principal-idèle connecting map, followed by fixed-unit descent. -/
@[simp]
theorem normObstructionCokernelEquivKnot_mk
    (c : Multiplicative (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L)) (-1))) :
    (normObstructionCokernelEquivKnot K L
      (QuotientGroup.mk' (ideleToClassTateMinusOne K L).range c) :
        Kˣ ⧸ localNormSubgroup K L) =
      normObstructionConnecting K L c :=
  rfl

end GlobalClassFieldTheory.ClassFieldAxiom
