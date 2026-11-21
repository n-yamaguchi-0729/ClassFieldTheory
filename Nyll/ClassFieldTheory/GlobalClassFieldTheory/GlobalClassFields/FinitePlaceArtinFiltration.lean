/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNorm
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.TowerRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFiltered

/-!
# Upper ramification under finite-place idele insertion

Global Artin applied to a single finite-place idele class carries its
principal-unit filtration onto the images of the actual local upper groups.
-/

@[expose] public section

noncomputable section

open scoped NumberField ValuativeRel

namespace GlobalClassFieldTheory.Reciprocity

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations LocalFieldTheory
open FunctionField (
  absoluteAbelianizedRestrictionOfEmbedding absoluteAbelianizedRestrictionOfEmbedding_mk
  absoluteRestrictionOfEmbedding absoluteRestrictionOfEmbedding_mk
  embeddedFiniteRestriction embeddedFiniteRestriction_commutes
)
open LocalClassFieldTheory RamificationTheory.LocalField

universe u v

private theorem map_map_of_comp_eq
    {G J Q T : Type*} [Group G] [Group J] [Group Q] [Group T]
    (H : Subgroup G) (i : G →* J) (f : J →* T) (j : G →* Q) (g : Q →* T)
    (h : f.comp i = g.comp j) : (H.map i).map f = (H.map j).map g :=
  (Subgroup.map_map H f i).trans
    ((congrArg (fun q : G →* T => H.map q) h).trans (Subgroup.map_map H g j).symm)

private theorem comp_mulEquiv_eq_of_apply_symm
    {U V G : Type*} [Group U] [Group V] [Group G]
    (e : U ≃* V) (f : V →* G) (g : U →* G) (h : ∀ x, f x = g (e.symm x)) :
    f.comp e.toMonoidHom = g := by
  apply MonoidHom.ext
  intro x
  exact (h (e x)).trans (congrArg g (e.symm_apply_apply x))

section Abelian

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

private theorem globalArtin_comp_localCompletionUnits
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    ((globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v)).comp
        eK.toMonoidHom =
      (finitePlaceLocalToGlobalMonoidHom v w).comp
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom vK.Completion E) := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner eK
  let toGlobal := finitePlaceLocalToGlobalMonoidHom v w
  let localArtin := LocalClassFieldTheory.abelianLocalArtinMonoidHom vK.Completion E
  have hlocal : (finitePlaceLocalArtinMonoidHom v w).comp eK.toMonoidHom = localArtin := by
    apply comp_mulEquiv_eq_of_apply_symm eK
    intro x
    have hEval := finitePlaceLocalArtinMonoidHom_apply_universe v w x
    dsimp (config := { instances := true, zetaDelta := true }) only
      [vK, E, eK, localArtin, algebraOwner, finiteOwner, abelianOwner, valuationOwner,
        localFieldOwner]
    with_reducible exact hEval
  have hcomp : (finitePlaceArtinMonoidHomOfExtension v w).comp eK.toMonoidHom =
      toGlobal.comp localArtin := by
    rw [finitePlaceArtinMonoidHomOfExtension_factor, MonoidHom.comp_assoc, hlocal]
  have hglobal : (globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v) =
      finitePlaceArtinMonoidHomOfExtension v w :=
    (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass (K := K) (L := L) v).trans
      (finitePlaceArtinMonoidHomOfExtension_eq v (chosenFinitePlaceExtension (L := L) v) w)
  exact (congrArg (fun f => f.comp eK.toMonoidHom) hglobal).trans hcomp

/-- Global Artin at one finite place sends principal units onto the image
of the corresponding upper group of the chosen localized extension. -/
theorem globalNormResidueMonoidHom_finitePlaceIdeleClass_fieldPrincipalUnits_of_extension
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) (t : ℝ) (ht : 0 ≤ t) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    ((fieldPrincipalUnits vK.Completion ⌈t⌉₊).map eK.toMonoidHom).map
        ((globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v)) =
      (localUpperRamificationGroup vK.Completion E t).map
        (finitePlaceLocalToGlobalMonoidHom v w) := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner eK
  let H := fieldPrincipalUnits vK.Completion ⌈t⌉₊
  let localArtin := LocalClassFieldTheory.abelianLocalArtinMonoidHom vK.Completion E
  let globalArtin := (globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v)
  let toGlobal := finitePlaceLocalToGlobalMonoidHom v w
  have h := map_map_of_comp_eq H eK.toMonoidHom globalArtin localArtin toGlobal
    (globalArtin_comp_localCompletionUnits v w)
  have hFiltered := LocalClassFieldTheory.Universe.finiteAbelian_filteredLocalReciprocity
    vK.Completion E t ht
  exact h.trans (congrArg (fun J => J.map toGlobal) hFiltered)

/-- Global Artin at one finite place sends principal units onto the image
of the corresponding upper group of the chosen localized extension. -/
theorem globalNormResidueMonoidHom_finitePlaceIdeleClass_fieldPrincipalUnits
    (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) (ht : 0 ≤ t) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    ((fieldPrincipalUnits vK.Completion ⌈t⌉₊).map eK.toMonoidHom).map
        ((globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v)) =
      (localUpperRamificationGroup vK.Completion E t).map (finitePlaceLocalToGlobalMonoidHom v w) :=
  globalNormResidueMonoidHom_finitePlaceIdeleClass_fieldPrincipalUnits_of_extension
    v (chosenFinitePlaceExtension (L := L) v) t ht

end Abelian

section Galois

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [NumberField L] in
private theorem finiteAbelianizedRestriction_eq_restrictScalars
    (i : L →ₐ[K] SeparableClosure K) (A : IntermediateField K L) [IsAbelianGalois K A]
    (e : Group.Abelianization Gal(L/K) ≃* Gal(A/K))
    (he : e.toMonoidHom.comp Group.Abelianization.of = AlgEquiv.restrictNormalHom A)
    (a : localAbsoluteAbelianProfinite K) :
    let j : A →ₐ[K] SeparableClosure K := i.comp (IsScalarTower.toAlgHom K A L)
    e (absoluteAbelianizedRestrictionOfEmbedding K L i a) =
      absoluteRestrictionOfEmbedding K A j a := by
  intro j
  refine QuotientGroup.induction_on a ?_
  intro σ
  rw [absoluteAbelianizedRestrictionOfEmbedding_mk, absoluteRestrictionOfEmbedding_mk]
  let q : Gal(L/K) →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  have hqApply : q (embeddedFiniteRestriction K L i σ) =
      embeddedFiniteRestriction K A j σ := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    calc
      j (q (embeddedFiniteRestriction K L i σ) x) =
          i (embeddedFiniteRestriction K L i σ (algebraMap A L x)) :=
        congrArg i (AlgEquiv.restrictNormal_commutes (embeddedFiniteRestriction K L i σ) A x)
      _ = σ (j x) := embeddedFiniteRestriction_commutes K L i σ (algebraMap A L x)
      _ = j (embeddedFiniteRestriction K A j σ x) :=
        (embeddedFiniteRestriction_commutes K A j σ x).symm
  exact (DFunLike.congr_fun he (embeddedFiniteRestriction K L i σ)).trans hqApply

omit [NumberField L] in
/-- The upper filtration descends along the actual finite-place
restriction on localized automorphisms. -/
private theorem finitePlaceUpperGroup_map_localRestriction
    (A : IntermediateField K L) [IsAbelianGalois K A]
    (v : HeightOneSpectrum (𝓞 K)) (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)
    (t : ℝ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let wA := restrictFinitePlaceExtension (E := A) v w
    let U := LocalizedCompletion vK w
    let UA := LocalizedCompletion vK wA
    let : Algebra vK.Completion U := finitePlaceLocalArtinLocalizedAlgebra v w
    let : Algebra vK.Completion UA := finitePlaceLocalArtinLocalizedAlgebra v wA
    let : FiniteDimensional vK.Completion U := finitePlaceLocalArtinFiniteDimensional v w
    let : FiniteDimensional vK.Completion UA := finitePlaceLocalArtinFiniteDimensional v wA
    let : IsGalois vK.Completion U := HilbertRamification.algebraicLocalization_isGalois vK w
    let : IsAbelianGalois vK.Completion UA :=
      finitePlaceLocalArtinIsAbelianGalois v wA inferInstance
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (localUpperRamificationGroup vK.Completion U t).map
        (finitePlaceLocalRestrictionMonoidHom (E := A) v w) =
      localUpperRamificationGroup vK.Completion UA t := by
  intro vK wA U UA aU aUA fU fUA gU gUA V localField
  let j := finitePlaceRestrictedLocalizedCompletionAlgHom (E := A) v w
  let a : Algebra UA U := j.toRingHom.toAlgebra
  let : SMul UA U := a.toSMul
  let : IsScalarTower vK.Completion UA U := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (j.commutes x).symm)
  let : IsGalois vK.Completion UA := gUA.toIsGalois
  have h := localUpperRamificationGroup_map_restrictNormalHom vK.Completion UA U t
  dsimp only [finitePlaceLocalRestrictionMonoidHom]
  dsimp (config := { instances := true, zetaDelta := true }) only
    [U, UA, vK, wA, j, a, aU, aUA, fU, fUA, gU, gUA, V, localField] at h ⊢
  with_reducible exact h

omit [NumberField L] in
private theorem finitePlaceUpperGroup_map_to_abelianSubfield
    (A : IntermediateField K L) [NumberField A] [IsAbelianGalois K A]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)
    (t : ℝ) (ht : 0 ≤ t) :
    let vK := HeightOneSpectrum.adicAbv K v
    let U := LocalizedCompletion vK w
    let : Algebra vK.Completion U := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion U := finitePlaceLocalArtinFiniteDimensional v w
    let : IsGalois vK.Completion U := HilbertRamification.algebraicLocalization_isGalois vK w
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    let P := (fieldPrincipalUnits vK.Completion ⌈t⌉₊).map eK.toMonoidHom
    (localUpperRamificationGroup vK.Completion U t).map
        ((AlgEquiv.restrictNormalHom A).comp (finitePlaceLocalToGlobalMonoidHom v w)) =
      P.map ((globalNormResidueMonoidHom K A).comp (IdeleGroup.finitePlaceIdeleClass v)) := by
  intro vK U algebraOwner finiteOwner galoisOwner valuationOwner localFieldOwner eK P
  let wA := restrictFinitePlaceExtension (E := A) v w
  let q : Gal(L/K) →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  let dL := finitePlaceLocalToGlobalMonoidHom v w
  let H := localUpperRamificationGroup vK.Completion U t
  have h₁ := finitePlaceDecompositionTransport_restrict_tower (E := A) v w
  have h₂ := finitePlaceUpperGroup_map_localRestriction A v w t
  have h₃ :=
    globalNormResidueMonoidHom_finitePlaceIdeleClass_fieldPrincipalUnits_of_extension v wA t ht
  change H.map (q.comp dL) = P.map _
  rw [h₁, ← Subgroup.map_map, h₂, ← h₃]

omit [NumberField L] in
/-- The finite projection of absolute global Artin on a one-place idele
class maps each principal-unit step onto the image of the corresponding
local upper group in the global Galois abelianization. -/
theorem mathlibGlobalArtin_abelianizedRestriction_finitePlaceIdeleClass_fieldPrincipalUnits
    (i : L →ₐ[K] SeparableClosure K) (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) (ht : 0 ≤ t) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let U := LocalizedCompletion vK w
    let : Algebra vK.Completion U := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion U := finitePlaceLocalArtinFiniteDimensional v w
    let : IsGalois vK.Completion U := HilbertRamification.algebraicLocalization_isGalois vK w
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    let art : IdeleClassGroup K →* localAbsoluteAbelianProfinite K :=
      (absoluteGaloisGroupAbelianizationEquivSeparable K).toMulEquiv.toMonoidHom.comp
        (mathlibGlobalArtin K).toMonoidHom
    ((fieldPrincipalUnits vK.Completion ⌈t⌉₊).map eK.toMonoidHom).map
        (((absoluteAbelianizedRestrictionOfEmbedding K L i).comp art).comp
          (IdeleGroup.finitePlaceIdeleClass v)) =
      (localUpperRamificationGroup vK.Completion U t).map
        (Group.Abelianization.of.comp (finitePlaceLocalToGlobalMonoidHom v w)) := by
  intro vK w U algebraOwner finiteOwner galoisOwner valuationOwner localFieldOwner eK art
  let H := commutator Gal(L/K)
  let A := IntermediateField.fixedField H
  let : NumberField A := NumberField.of_module_finite K A
  let : IsGalois K A := IsGalois.of_fixedField_normal_subgroup H
  let e : Group.Abelianization Gal(L/K) ≃* Gal(A/K) := IsGalois.normalAutEquivQuotient H
  let : IsAbelianGalois K A :=
    { toIsGalois := inferInstance
      toIsMulCommutative := e.surjective.isMulCommutative }
  let j := i.comp (IsScalarTower.toAlgHom K A L)
  let q : Gal(L/K) →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  have he : e.toMonoidHom.comp Group.Abelianization.of = q := by
    apply MonoidHom.ext
    exact IsGalois.normalAutEquivQuotient_apply H
  let α := ((absoluteAbelianizedRestrictionOfEmbedding K L i).comp art).comp
    (IdeleGroup.finitePlaceIdeleClass v)
  let lowerArt := (globalNormResidueMonoidHom K A).comp (IdeleGroup.finitePlaceIdeleClass v)
  have hArtin : e.toMonoidHom.comp α = lowerArt := by
    apply MonoidHom.ext
    intro x
    exact (finiteAbelianizedRestriction_eq_restrictScalars i A e he
      (art (IdeleGroup.finitePlaceIdeleClass v x))).trans
      (mathlibGlobalArtin_restrictionOfEmbedding K A j (IdeleGroup.finitePlaceIdeleClass v x))
  let P : Subgroup (v.adicCompletion K)ˣ :=
    (fieldPrincipalUnits vK.Completion ⌈t⌉₊).map eK.toMonoidHom
  let Hupper : Subgroup Gal(U/vK.Completion) := localUpperRamificationGroup vK.Completion U t
  let dL : Gal(U/vK.Completion) →* Gal(L/K) := finitePlaceLocalToGlobalMonoidHom v w
  let ab : Gal(L/K) →* Group.Abelianization Gal(L/K) := Group.Abelianization.of
  let : NumberField L := NumberField.of_module_finite K L
  have hUpper := finitePlaceUpperGroup_map_to_abelianSubfield A v w t ht
  have hcomp : e.toMonoidHom.comp (ab.comp dL) = q.comp dL := by
    rw [← MonoidHom.comp_assoc, he]
  have hLeft : (P.map α).map e.toMonoidHom = P.map lowerArt :=
    (Subgroup.map_map P e.toMonoidHom α).trans
      (congrArg (fun φ => P.map φ) hArtin)
  have hRight : (Hupper.map (ab.comp dL)).map e.toMonoidHom = Hupper.map (q.comp dL) :=
    (Subgroup.map_map Hupper e.toMonoidHom (ab.comp dL)).trans
      (congrArg (fun φ => Hupper.map φ) hcomp)
  have hImage : (P.map α).map e.toMonoidHom = (Hupper.map (ab.comp dL)).map e.toMonoidHom := by
    rw [hLeft, hRight]
    dsimp only at hUpper
    dsimp (config := { instances := true, zetaDelta := true }) only
      [P, lowerArt, Hupper, q, dL, eK, U, vK, A, algebraOwner, finiteOwner,
        galoisOwner, valuationOwner, localFieldOwner]
    with_reducible exact hUpper.symm
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective hImage

end Galois

end GlobalClassFieldTheory.Reciprocity
