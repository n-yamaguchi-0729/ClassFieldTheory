/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteNormCoordinates
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm

/-!
# Norm naturality of the specified absolute Artin map

The original absolute Galois restriction and the actual idèle-class norm
intertwine the specified Mathlib-valued Artin maps. The proof checks the
existing finite Artin norm square at every finite abelian coordinate; it
does not construct another reciprocity map.
-/

@[expose] public section

open scoped NumberField
open NumberField ClassFieldTheory LocalClassFieldTheory
open ProCGroups.Abelian FunctionField

noncomputable section

universe u v w

namespace GlobalClassFieldTheory.Reciprocity

private noncomputable abbrev nativeArtinValue (K : Type u) [Field K] [NumberField K]
    (c : NumberField.IdeleClassGroup (𝓞 K) K) : localAbsoluteAbelianProfinite K :=
  absoluteGaloisGroupAbelianizationEquivSeparable K (mathlibGlobalArtin K c)

/-- Restriction of standard absolute Artin through a chosen embedding
recovers the actual finite abelian norm-residue map. -/
theorem mathlibGlobalArtin_restrictionOfEmbedding
    (K : Type u) (E : Type w) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsAbelianGalois K E]
    (i : E →ₐ[K] SeparableClosure K) (c : IdeleClassGroup K) :
    absoluteRestrictionOfEmbedding K E i
      (absoluteGaloisGroupAbelianizationEquivSeparable K (mathlibGlobalArtin K c)) =
      globalNormResidueMonoidHom K E c := by
  let e := i.equivFieldRange
  let : FiniteDimensional K i.fieldRange := e.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois K i.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hi : i.fieldRange ≤ maximalAbelianExtension K :=
    finiteAbelianIntermediateField_le_maximalAbelianExtension K i.fieldRange
  let j : E →ₐ[K] maximalAbelianExtension K :=
    i.codRestrict (maximalAbelianExtension K).toSubalgebra
      (fun x => hi (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let : Algebra E (maximalAbelianExtension K) := j.toAlgebra
  have : IsScalarTower K E (maximalAbelianExtension K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  have hcoordinate (q : localAbsoluteAbelianProfinite K) :
      absoluteRestrictionOfEmbedding K E i q = AlgEquiv.restrictNormalHom E
        (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K q) := by
    refine QuotientGroup.induction_on q ?_
    intro σ
    rw [absoluteRestrictionOfEmbedding_mk]
    change embeddedFiniteRestriction K E i σ = AlgEquiv.restrictNormalHom E
      (absoluteAbelianizationMulEquivMaximalAbelianGalois K (QuotientGroup.mk σ))
    rw [absoluteAbelianizationMulEquivMaximalAbelianGalois_mk]
    apply AlgEquiv.ext
    intro x
    apply i.injective
    have htop := AlgEquiv.restrictNormal_commutes σ (maximalAbelianExtension K) (j x)
    have hbottom := AlgEquiv.restrictNormal_commutes
      (AlgEquiv.restrictNormalHom (maximalAbelianExtension K) σ) E x
    exact (embeddedFiniteRestriction_commutes K E i σ x).trans
      ((congrArg Subtype.val hbottom).trans htop).symm
  refine (hcoordinate (nativeArtinValue K c)).trans ?_
  change AlgEquiv.restrictNormalHom E
    (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K c)) = _
  exact mathlibGlobalArtin_finiteProjection_standard_of_scalarTower (K := K) E c

private theorem nativeArtinValue_norm_finiteCoordinate
    (K : Type u) (F : Type v) (E : Type w)
    [Field K] [NumberField K] [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra K F] [Algebra K E] [FiniteDimensional K F]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (i : E →ₐ[K] SeparableClosure K) (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    absoluteRestrictionOfEmbedding K E i
        (nativeAbsoluteAbelianMap (algebraMap K F) (nativeArtinValue F c)) =
      standardNumberFieldArtinContinuousMonoidHom K E (NumberField.IdeleClassGroup.norm K F c) := by
  let T := normCoordinateField K F E i
  let j : E →+* T := normCoordinateEmbedding K F E i
  let : NumberField T := NumberField.of_module_finite F T
  let : Algebra K T := ((algebraMap F T).comp (algebraMap K F)).toAlgebra
  let : Algebra E T := j.toAlgebra
  have : IsScalarTower K F T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K E T := IsScalarTower.of_algebraMap_eq
    (fun a => (normCoordinateEmbedding_algebraMap K F E i a).symm)
  have hcoordinate (q : localAbsoluteAbelianProfinite F) :
      absoluteRestrictionOfEmbedding K E i (nativeAbsoluteAbelianMap (algebraMap K F) q) =
        AlgEquiv.restrictNormalHom E
          ((absoluteRestrictionOfEmbedding F T T.val q).restrictScalars K) := by
    refine QuotientGroup.induction_on q ?_
    intro σ
    rw [nativeAbsoluteAbelianMap_mk, absoluteRestrictionOfEmbedding_mk,
      absoluteRestrictionOfEmbedding_mk]
    have hT : embeddedFiniteRestriction F T T.val σ = AlgEquiv.restrictNormalHom T σ := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (embeddedFiniteRestriction_commutes F T T.val σ x).trans
        (AlgEquiv.restrictNormal_commutes σ T x).symm
    rw [hT]
    apply AlgEquiv.ext
    intro x
    apply j.injective
    exact (normCoordinateEmbedding_restrict K F E i σ x).trans
      ((AlgEquiv.restrictNormalHom T σ).restrictScalars K |>.restrictNormal_commutes E x).symm
  rw [hcoordinate, mathlibGlobalArtin_restrictionOfEmbedding F T T.val]
  exact standardNumberFieldArtin_norm_restriction (K := K) (L := E) (M := F) (N := T) c

private theorem nativeArtinValue_norm
    (K : Type u) (F : Type v) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [FiniteDimensional K F] (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    nativeAbsoluteAbelianMap (algebraMap K F) (nativeArtinValue F c) =
      nativeArtinValue K (NumberField.IdeleClassGroup.norm K F c) := by
  apply ProfiniteGrp.toLimit_injective (localAbsoluteAbelianProfinite K)
  apply Subtype.ext
  funext N
  apply (absoluteFiniteQuotientEquiv K N).injective
  let E := absoluteFiniteQuotientField K N
  let : NumberField E := NumberField.of_module_finite K E
  have hrestriction (q : localAbsoluteAbelianProfinite K) :
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk q) =
        absoluteRestrictionOfEmbedding K E E.val q := by
    refine QuotientGroup.induction_on q ?_
    intro σ
    rw [absoluteFiniteQuotientEquiv_mk_mk, absoluteRestrictionOfEmbedding_mk]
    apply AlgEquiv.ext
    intro x
    apply E.val.injective
    exact (AlgEquiv.restrictNormal_commutes σ E x).trans
      (embeddedFiniteRestriction_commutes K E E.val σ x).symm
  change absoluteFiniteQuotientEquiv K N
      (QuotientGroup.mk (nativeAbsoluteAbelianMap (algebraMap K F) (nativeArtinValue F c))) =
    absoluteFiniteQuotientEquiv K N
      (QuotientGroup.mk (nativeArtinValue K (NumberField.IdeleClassGroup.norm K F c)))
  rw [hrestriction, hrestriction, nativeArtinValue_norm_finiteCoordinate K F E E.val,
    mathlibGlobalArtin_restrictionOfEmbedding K E E.val]
  rfl

private theorem mathlibAbsoluteMap_toSeparable
    {K : Type u} {L : Type v} [Field K] [Field L] (f : K →+* L)
    (q : Field.absoluteGaloisGroupAbelianization L) :
    absoluteGaloisGroupAbelianizationEquivSeparable K
        (TopologicalAbelianization.map (Field.absoluteGaloisGroup.map f) q) =
      nativeAbsoluteAbelianMap f (absoluteGaloisGroupAbelianizationEquivSeparable L q) := by
  refine QuotientGroup.induction_on q ?_
  intro σ
  let fAbs := Field.absoluteGaloisGroup.map f
  let qK := absoluteGaloisGroupAbelianizationEquivSeparable K
  have hmap := congrArg qK (TopologicalAbelianization.map_apply_mk fAbs σ)
  have hK := absoluteGaloisGroupAbelianizationEquivSeparable_mk K (fAbs σ)
  have hL := congrArg (nativeAbsoluteAbelianMap f)
    (absoluteGaloisGroupAbelianizationEquivSeparable_mk L σ)
  have hNative := nativeAbsoluteAbelianMap_mk f (AlgEquiv.separableClosure σ)
  refine hmap.trans (hK.trans (Eq.trans ?_ (hL.trans hNative).symm))
  apply congrArg (QuotientGroup.mk : Gal(SeparableClosure K/K) → localAbsoluteAbelianProfinite K)
  have hσ : AlgEquiv.separableClosure σ =
      ValuationTheory.Completion.separableClosureAutEquiv L σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (ValuationTheory.Completion.separableClosureAutEquiv_apply L σ x).symm
  rw [hσ]
  change AlgEquiv.separableClosure (Field.absoluteGaloisGroup.map f σ) =
    ValuationTheory.Completion.separableClosureAutEquiv K
      (Field.absoluteGaloisGroup.map f
        ((ValuationTheory.Completion.separableClosureAutEquiv L).symm
          (ValuationTheory.Completion.separableClosureAutEquiv L σ)))
  let g := ValuationTheory.Completion.separableClosureAutEquiv L
  let h := ValuationTheory.Completion.separableClosureAutEquiv K
  have hinv := congrArg (fun τ : Field.absoluteGaloisGroup L => h (fAbs τ)) (g.symm_apply_apply σ)
  refine Eq.trans ?_ hinv.symm
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (ValuationTheory.Completion.separableClosureAutEquiv_apply K (fAbs σ) x).symm

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- Absolute norm naturality uses the original absolute Galois restriction
and the specified geometric Artin maps, with no Galois assumption on `L/K`. -/
theorem mathlibGlobalArtin_norm (c : NumberField.IdeleClassGroup (𝓞 L) L) :
    TopologicalAbelianization.map (Field.absoluteGaloisGroup.map (algebraMap K L))
        (mathlibGlobalArtin L c) =
      mathlibGlobalArtin K (NumberField.IdeleClassGroup.norm K L c) := by
  apply (absoluteGaloisGroupAbelianizationEquivSeparable K).injective
  rw [mathlibAbsoluteMap_toSeparable]
  exact nativeArtinValue_norm K L c

end GlobalClassFieldTheory.Reciprocity
