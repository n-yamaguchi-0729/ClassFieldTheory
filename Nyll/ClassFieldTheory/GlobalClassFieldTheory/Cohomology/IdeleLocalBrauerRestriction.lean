/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.LocalizationNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleBrauerBaseRestriction

/-! # Placewise Brauer restriction for full idèle cohomology -/

@[expose] public section

open AlgebraicNumberTheory.Valuations CategoryTheory ClassFieldTheory.Brauer
open ClassFieldTower.Martinet.Shafarevich IsDedekindDomain NumberField
open scoped NumberField TensorProduct

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

attribute [local instance] scalarTensorUnitsAction

section InfiniteTensorEvaluation

attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

variable {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

private theorem infiniteTensorH2ToBrauer_evaluate
    (v : InfinitePlace K) (i : E →ₐ[K] SeparableClosure v.Completion) :
    infiniteTensorH2ToBrauerOfExtension E v = absoluteTensorH2Map i :=
  tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ i

end InfiniteTensorEvaluation

section Coordinates

attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E] [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional M E]
  [FiniteDimensional K E] [IsGalois K E] [IsGalois M E]

local notation "I[" F "]" =>
  (ShortComplex.X₂ (C := Rep ℤ Gal(E/F)) (finiteIdeleShortComplex F E))
local notation "r" => (AlgEquiv.restrictScalarsHom K : Gal(E/M) →* Gal(E/K))

/-- Restriction on actual idèle cohomology to an intermediate base field. -/
def fullIdeleH2BaseRestriction : groupCohomology I[K] 2 ⟶ groupCohomology I[M] 2 :=
  groupCohomology.map r (relativeIdeleBaseRestrictionRepHom (K₀ := K) (M₀ := M) (L₀ := E)) 2

/-- The absolute finite Brauer coordinate of a full idèle cohomology class. -/
def fullIdeleFiniteBrauerCoordinate (v : HeightOneSpectrum (𝓞 K)) :
    groupCohomology I[K] 2 →+ Br (v.adicCompletion K) :=
  (finiteTensorH2ToBrauerOfExtension E v).comp
    (groupCohomology.map (A := I[K]) (MonoidHom.id (Gal(E/K)))
      (finiteIdeleFiniteTensorRepHom K E v) 2).hom.toAddMonoidHom

/-- Evaluation in degree two at the archimedean tensor factor of the actual idèles. -/
def fullIdeleInfiniteTensorH2Coordinate (v : InfinitePlace K) :
    groupCohomology I[K] 2 ⟶
      groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) (v.Completion ⊗[K] E)ˣ) 2 :=
  groupCohomology.map (A := I[K]) (MonoidHom.id (Gal(E/K)))
    (finiteIdeleInfiniteTensorRepHom K E v) 2

/-- The absolute archimedean Brauer coordinate of a full idèle cohomology class. -/
def fullIdeleInfiniteBrauerCoordinate (v : InfinitePlace K) :
    groupCohomology I[K] 2 →+ Br v.Completion :=
  (infiniteTensorH2ToBrauerOfExtension E v).comp
    (fullIdeleInfiniteTensorH2Coordinate (E := E) v).hom.toAddMonoidHom

omit [NumberField E] in
theorem fullIdeleInfiniteBrauerCoordinate_apply (v : InfinitePlace K)
    (a : groupCohomology I[K] 2) :
    fullIdeleInfiniteBrauerCoordinate (E := E) v a =
      infiniteTensorH2ToBrauerOfExtension E v
        (fullIdeleInfiniteTensorH2Coordinate (E := E) v a) :=
  rfl

omit [NumberField E] in
/-- Restricting a full idèle class gives the ordinary restriction at each finite completion. -/
theorem fullIdeleFiniteBrauerCoordinate_baseRestriction
    (W : HeightOneSpectrum (𝓞 M)) (x : groupCohomology I[K] 2) :
    let v := finitePlaceBelow (K := K) W
    fullIdeleFiniteBrauerCoordinate (E := E) W (fullIdeleH2BaseRestriction (M := M) x) =
      restrict (finitePlaceAdicCompletionMap K M v ⟨W, rfl⟩)
        (fullIdeleFiniteBrauerCoordinate (E := E) v x) := by
  intro v
  let F := v.adicCompletion K
  let H := W.adicCompletion M
  let i : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
  let j : E →ₐ[M] SeparableClosure H := IsSepClosed.lift
  have hc := ConcreteCategory.congr_hom
    (finiteIdeleH2_finiteTensor_baseRestriction (K₀ := K) (M₀ := M) (L₀ := E) W) x
  change finiteTensorH2ToBrauerOfExtension E W
      ((groupCohomology.map (A := I[M]) (MonoidHom.id (Gal(E/M)))
        (finiteIdeleFiniteTensorRepHom M E W) 2)
        (fullIdeleH2BaseRestriction (M := M) x)) = _
  rw [show (groupCohomology.map (A := I[M]) (MonoidHom.id (Gal(E/M)))
      (finiteIdeleFiniteTensorRepHom M E W) 2)
      (fullIdeleH2BaseRestriction (M := M) x) = _ from hc]
  change finiteTensorH2ToBrauerOfExtension E W _ =
    restrict (finiteCompletionBaseRestriction K M W).toRingHom
      (finiteTensorH2ToBrauerOfExtension E v _)
  simp only [finiteTensorH2ToBrauerOfExtension]
  rw [tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ j,
    tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ i]
  exact absoluteTensorH2Map_baseRestriction (finiteCompletionBaseRestriction K M W) i j _

omit [NumberField E] [FiniteDimensional K M] in
private theorem infiniteTensorH2ToBrauer_baseRestriction
    (W : InfinitePlace M) :
    let v := infinitePlaceBelow (K := K) W
    let f : v.Completion →ₐ[K] W.Completion := infiniteCompletionBaseRestriction K M W
    let _ : IsScalarTower K M W.Completion := infiniteCompletionBaseTower K M W
    ∀ a : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) (v.Completion ⊗[K] E)ˣ) 2,
      infiniteTensorH2ToBrauerOfExtension E W
          (groupCohomology.map r (localTensorBaseRestrictionRepHom (M₀ := M) (L₀ := E) f) 2 a) =
        restrict (K := v.Completion) (L := W.Completion) (infinitePlaceBrauerCompletionMap v W rfl)
          (infiniteTensorH2ToBrauerOfExtension E v a) := by
  intro v f hTower a
  let F := v.Completion
  let H := W.Completion
  let i : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
  let j : E →ₐ[M] SeparableClosure H := IsSepClosed.lift
  let t := groupCohomology.map r (localTensorBaseRestrictionRepHom (M₀ := M) (L₀ := E) f) 2
  let u := restrict f.toRingHom
  have hLow := DFunLike.congr_fun (infiniteTensorH2ToBrauer_evaluate v i) a
  have hHigh := DFunLike.congr_fun (infiniteTensorH2ToBrauer_evaluate W j) (t a)
  have hMap := absoluteTensorH2Map_baseRestriction f i j a
  have hRing : f.toRingHom = infinitePlaceBrauerCompletionMap v W rfl := rfl
  rw [← hRing]
  exact hHigh.trans (hMap.trans (congrArg u hLow.symm))

omit [NumberField E] [FiniteDimensional M E] [FiniteDimensional K E]
  [IsGalois K E] [IsGalois M E] in
private theorem fullIdeleInfiniteTensorH2Coordinate_baseRestriction
    (W : InfinitePlace M) :
    let v := infinitePlaceBelow (K := K) W
    let f : v.Completion →ₐ[K] W.Completion := infiniteCompletionBaseRestriction K M W
    let _ : IsScalarTower K M W.Completion := infiniteCompletionBaseTower K M W
    fullIdeleH2BaseRestriction (K := K) (M := M) (E := E) ≫
      fullIdeleInfiniteTensorH2Coordinate (E := E) W =
    fullIdeleInfiniteTensorH2Coordinate (E := E) v ≫
      groupCohomology.map r (localTensorBaseRestrictionRepHom (M₀ := M) (L₀ := E) f) 2 := by
  intro v f hTower
  exact finiteIdeleH2_infiniteTensor_baseRestriction (K₀ := K) (M₀ := M) (L₀ := E) W

omit [NumberField E] in
/-- Restricting a full idèle class gives the ordinary restriction at each infinite completion. -/
theorem fullIdeleInfiniteBrauerCoordinate_baseRestriction
    (W : InfinitePlace M) (x : groupCohomology I[K] 2) :
    let v := infinitePlaceBelow (K := K) W
    fullIdeleInfiniteBrauerCoordinate (E := E) W (fullIdeleH2BaseRestriction (M := M) x) =
      restrict (infinitePlaceBrauerCompletionMap v W rfl)
        (fullIdeleInfiniteBrauerCoordinate (E := E) v x) := by
  dsimp only
  have hCoordinate := ConcreteCategory.congr_hom
    (fullIdeleInfiniteTensorH2Coordinate_baseRestriction (K := K) (E := E) W) x
  simp only [ConcreteCategory.comp_apply] at hCoordinate
  have hRestriction := infiniteTensorH2ToBrauer_baseRestriction (K := K) (E := E) W
    (fullIdeleInfiniteTensorH2Coordinate (K := K) (E := E) (infinitePlaceBelow (K := K) W) x)
  with_reducible
    simpa only [fullIdeleInfiniteBrauerCoordinate_apply, hCoordinate] using hRestriction

end Coordinates

section Splitting

attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

/-- A finite coordinate of full idèle cohomology splits at every upper completion. -/
theorem fullIdeleFiniteBrauerCoordinate_restrict_top
    (W : HeightOneSpectrum (𝓞 E)) (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) :
    let v := finitePlaceBelow (K := K) W
    restrict (finitePlaceAdicCompletionMap K E v ⟨W, rfl⟩)
      (fullIdeleFiniteBrauerCoordinate (E := E) v x) = 0 := by
  intro v
  let F := v.adicCompletion K
  let i : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
  change restrict (finiteCompletionBaseRestriction K E W).toRingHom
    (finiteTensorH2ToBrauerOfExtension E v _) = 0
  simp only [finiteTensorH2ToBrauerOfExtension]
  rw [tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ i]
  exact restrict_absoluteTensorH2Map_eq_zero_of_embedding (finiteCompletionBaseRestriction K E W)
    i _

private theorem infiniteTensorH2ToBrauer_restrict_top
    (W : InfinitePlace E) :
    let v := infinitePlaceBelow (K := K) W
    let _ : IsScalarTower K E W.Completion := infiniteCompletionBaseTower K E W
    ∀ a : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) (v.Completion ⊗[K] E)ˣ) 2,
      restrict (K := v.Completion) (L := W.Completion) (infinitePlaceBrauerCompletionMap v W rfl)
        (infiniteTensorH2ToBrauerOfExtension E v a) = 0 := by
  intro v hTower a
  let f : v.Completion →ₐ[K] W.Completion := infiniteCompletionBaseRestriction K E W
  let i : E →ₐ[K] SeparableClosure v.Completion := IsSepClosed.lift
  let u := restrict f.toRingHom
  have hv := DFunLike.congr_fun (infiniteTensorH2ToBrauer_evaluate v i) a
  have h := restrict_absoluteTensorH2Map_eq_zero_of_embedding f i a
  have hRing : f.toRingHom = infinitePlaceBrauerCompletionMap v W rfl := rfl
  rw [← hRing]
  exact (congrArg u hv).trans h

/-- An infinite coordinate of full idèle cohomology splits at every upper completion. -/
theorem fullIdeleInfiniteBrauerCoordinate_restrict_top
    (W : InfinitePlace E) (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) :
    let v := infinitePlaceBelow (K := K) W
    restrict (infinitePlaceBrauerCompletionMap v W rfl)
      (fullIdeleInfiniteBrauerCoordinate (E := E) v x) = 0 := by
  dsimp only
  have hSplits := infiniteTensorH2ToBrauer_restrict_top (K := K) (E := E) W
    (fullIdeleInfiniteTensorH2Coordinate (K := K) (E := E) (infinitePlaceBelow (K := K) W) x)
  with_reducible
    simpa only [fullIdeleInfiniteBrauerCoordinate_apply] using hSplits

end Splitting

end GlobalClassFieldTheory.Cohomology
