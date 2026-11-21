/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FieldInclusion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteIdeleLocalH2

/-! # Local tensor coordinates when restricting the base of a relative idèle -/

@[expose] public section

open AlgebraicNumberTheory.Valuations CategoryTheory ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped NumberField TensorProduct

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

universe u v w

variable (K : Type u) (M : Type v) (L : Type w)
  [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]

/-- The local scalar-extension map on tensors with a fixed right factor. -/
def localTensorBaseRestriction {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra M B] [IsScalarTower K M B]
    (f : A →ₐ[K] B) : A ⊗[K] L →ₐ[K] B ⊗[M] L :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (R := M) (S := K) (B := L)).comp f)
    ((Algebra.TensorProduct.includeRight (R := M) (A := B)).restrictScalars K)
    (fun _ _ => Commute.all _ _)

omit [NumberField K] [NumberField M] [NumberField L] in
theorem localTensorBaseRestriction_tmul {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra M B] [IsScalarTower K M B]
    (f : A →ₐ[K] B) (a : A) (x : L) :
    localTensorBaseRestriction K M L f (a ⊗ₜ[K] x) = f a ⊗ₜ[M] x := by
  rw [localTensorBaseRestriction, Algebra.TensorProduct.lift_tmul]
  change (f a ⊗ₜ[M] (1 : L)) * ((1 : B) ⊗ₜ[M] x) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [NumberField K] [NumberField M] [NumberField L] in
/-- The local map intertwines the restricted action on the unchanged top field. -/
theorem localTensorBaseRestriction_conjugation {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra M B] [IsScalarTower K M B]
    (f : A →ₐ[K] B) (σ : Gal(L/M)) (z : A ⊗[K] L) :
    localTensorBaseRestriction K M L f (scalarTensorConjugation (σ.restrictScalars K) z) =
      scalarTensorConjugation σ (localTensorBaseRestriction K M L f z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    rw [scalarTensorConjugation_tmul, localTensorBaseRestriction_tmul,
      localTensorBaseRestriction_tmul, scalarTensorConjugation_tmul]
    rfl

/-- The canonical finite completion homomorphism as a lower-field algebra map. -/
def finiteCompletionBaseRestriction (W : HeightOneSpectrum (𝓞 M)) :
    (finitePlaceBelow (K := K) W).adicCompletion K →ₐ[K] W.adicCompletion M := by
  let V := finitePlaceBelow (K := K) W
  let W₀ : {w : HeightOneSpectrum (𝓞 M) // finitePlaceBelow (K := K) w = V} := ⟨W, rfl⟩
  refine ⟨finitePlaceAdicCompletionMap K M V W₀, fun x => ?_⟩
  change finitePlaceAdicCompletionMap K M V W₀ (x : V.adicCompletion K) =
    algebraMap K (W.adicCompletion M) x
  exact (finitePlaceAdicCompletionMap_coe K M V W₀ x).trans
    (IsScalarTower.algebraMap_apply K M (W.adicCompletion M) x).symm

/-- Scalar extension from a lower finite completion, on actual local tensors. -/
def finiteTensorBaseRestriction (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceBelow (K := K) W).adicCompletion K ⊗[K] L) →ₐ[K]
      W.adicCompletion M ⊗[M] L :=
  localTensorBaseRestriction K M L (finiteCompletionBaseRestriction K M W)

/-- The canonical archimedean completion homomorphism as a lower-field algebra map. -/
def infiniteCompletionBaseRestriction (W : InfinitePlace M) :
    (infinitePlaceBelow (K := K) W).Completion →ₐ[K] W.Completion := by
  let V := infinitePlaceBelow (K := K) W
  let : W.1.LiesOver V.1 := ⟨rfl⟩
  let : IsScalarTower K M W.Completion := IsScalarTower.of_algebraMap_eq' rfl
  refine { AbsoluteValue.Completion.map V.1 W.1 with commutes' := fun x => ?_ }
  change AbsoluteValue.Completion.map V.1 W.1 (algebraMap K V.Completion x) =
    algebraMap K W.Completion x
  rw [IsScalarTower.algebraMap_apply K M W.Completion x]
  simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, WithAbs.map_apply, WithAbs.ofAbs_toAbs] using
    (AbsoluteValue.Completion.map_coe V.1 W.1 (WithAbs.toAbs V.1 x))

omit [NumberField K] [NumberField M] in
/-- The lower scalar action on the upper archimedean completion factors through its field. -/
theorem infiniteCompletionBaseTower (W : InfinitePlace M) :
    IsScalarTower K M W.Completion := IsScalarTower.of_algebraMap_eq' rfl

/-- Scalar extension from a lower archimedean completion, on actual local tensors. -/
def infiniteTensorBaseRestriction (W : InfinitePlace M) :
    ((infinitePlaceBelow (K := K) W).Completion ⊗[K] L) →ₐ[K] W.Completion ⊗[M] L :=
  let _ : IsScalarTower K M W.Completion := infiniteCompletionBaseTower K M W
  localTensorBaseRestriction K M L (infiniteCompletionBaseRestriction K M W)

variable [FiniteDimensional K M] [FiniteDimensional M L]

/-- Re-express a relative adele with the intermediate field as its base. -/
def relativeAdeleBaseRestriction : RelativeAdeleRing K L ≃+* RelativeAdeleRing M L :=
  (towerRelativeAdeleRingEquiv K M L).symm.trans (towerActualRelativeAdeleRingEquiv K M L)

omit [NumberField L] [FiniteDimensional M L] in
theorem relativeAdeleBaseRestriction_tmul (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleBaseRestriction K M L (a ⊗ₜ[K] x) =
      NumberField.AdeleRing.fieldInclusion K M a ⊗ₜ[M] x := by
  change towerActualRelativeAdeleRingEquiv K M L
    (towerRelativeAdeleUnflatten K M L (a ⊗ₜ[K] x)) = _
  rw [towerRelativeAdeleUnflatten_tmul, bottomAdeleToTower_apply, topFieldToTower_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, towerActualRelativeAdeleRingEquiv_tmul,
    NumberField.AdeleRing.fieldInclusion_apply]
  rfl

omit [NumberField L] [FiniteDimensional M L] in
/-- The actual finite tensor coordinates over the two bases are compared by
completion scalar extension. -/
theorem relativeAdeleBaseRestriction_finite (W : HeightOneSpectrum (𝓞 M))
    (a : RelativeAdeleRing K L) :
    relativeAdeleFiniteComponent (K := M) (L := L) W (relativeAdeleBaseRestriction K M L a) =
      finiteTensorBaseRestriction K M L W
        (relativeAdeleFiniteComponent (K := K) (L := L) (finitePlaceBelow (K := K) W) a) := by
  induction a using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul b x =>
    rw [relativeAdeleBaseRestriction_tmul, relativeAdeleFiniteComponent_tmul,
      relativeAdeleFiniteComponent_tmul, NumberField.AdeleRing.fieldInclusion_finite,
      finiteTensorBaseRestriction, localTensorBaseRestriction_tmul, finiteCompletionBaseRestriction]
    rfl

omit [NumberField L] [FiniteDimensional M L] in
/-- The actual archimedean tensor coordinates over the two bases are compared
by completion scalar extension. -/
theorem relativeAdeleBaseRestriction_infinite (W : InfinitePlace M) (a : RelativeAdeleRing K L) :
    relativeAdeleInfiniteComponent (K := M) (L := L) W (relativeAdeleBaseRestriction K M L a) =
      infiniteTensorBaseRestriction K M L W
        (relativeAdeleInfiniteComponent (K := K) (L := L) (infinitePlaceBelow (K := K) W) a) := by
  induction a using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul b x =>
    rw [relativeAdeleBaseRestriction_tmul, relativeAdeleInfiniteComponent_tmul,
      relativeAdeleInfiniteComponent_tmul, NumberField.AdeleRing.fieldInclusion_infinite,
      infiniteTensorBaseRestriction, localTensorBaseRestriction_tmul,
      infiniteCompletionBaseRestriction]
    rfl

omit [NumberField L] [FiniteDimensional M L] in
/-- The same finite-coordinate compatibility on actual idèle units. -/
theorem relativeIdeleBaseRestriction_finite (W : HeightOneSpectrum (𝓞 M))
    (a : RelativeIdeleGroup K L) :
    RelativeIdeleGroup.finiteComponent (K := M) (L := L) W
        (towerRelativeIdeleBaseChangeMulEquiv K M L ((towerRelativeIdeleEquiv K M L).symm a)) =
      Units.map (finiteTensorBaseRestriction K M L W).toRingHom
        (RelativeIdeleGroup.finiteComponent (K := K) (L := L) (finitePlaceBelow (K := K) W) a) := by
  apply Units.ext
  exact relativeAdeleBaseRestriction_finite K M L W (a : RelativeAdeleRing K L)

omit [NumberField L] [FiniteDimensional M L] in
/-- The same archimedean-coordinate compatibility on actual idèle units. -/
theorem relativeIdeleBaseRestriction_infinite (W : InfinitePlace M) (a : RelativeIdeleGroup K L) :
    RelativeIdeleGroup.infiniteComponent (K := M) (L := L) W
        (towerRelativeIdeleBaseChangeMulEquiv K M L ((towerRelativeIdeleEquiv K M L).symm a)) =
      Units.map (infiniteTensorBaseRestriction K M L W).toRingHom
        (RelativeIdeleGroup.infiniteComponent (K := K) (L := L)
          (infinitePlaceBelow (K := K) W) a) := by
  apply Units.ext
  exact relativeAdeleBaseRestriction_infinite K M L W (a : RelativeAdeleRing K L)

section Cohomology

variable {K₀ M₀ L₀ : Type}
  [Field K₀] [NumberField K₀] [Field M₀] [NumberField M₀] [Field L₀] [NumberField L₀]
  [Algebra K₀ M₀] [Algebra M₀ L₀] [Algebra K₀ L₀] [IsScalarTower K₀ M₀ L₀]
  [FiniteDimensional K₀ M₀] [FiniteDimensional M₀ L₀]
  [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀] [IsGalois M₀ L₀]

local notation "r" => (AlgEquiv.restrictScalarsHom K₀ : Gal(L₀/M₀) →* Gal(L₀/K₀))
local notation "I[" F "]" =>
  (ShortComplex.X₂ (C := Rep ℤ Gal(L₀/F)) (finiteIdeleShortComplex F L₀))
local notation "T[" F "," A "]" => Rep.ofMulDistribMulAction Gal(L₀/F) (A ⊗[F] L₀)ˣ

local instance (F A : Type) [Field F] [Algebra F L₀] [CommRing A] [Algebra F A] :
    MulDistribMulAction Gal(L₀/F) (A ⊗[F] L₀)ˣ := scalarTensorUnitsAction

/-- The fixed-top idèle coefficient map for restriction to the intermediate Galois group. -/
def relativeIdeleBaseRestrictionRepHom : Rep.res r I[K₀] ⟶ I[M₀] := by
  let e := (towerRelativeIdeleEquiv K₀ M₀ L₀).symm.trans
    (towerRelativeIdeleBaseChangeMulEquiv K₀ M₀ L₀)
  refine Rep.ofHom (e.toMonoidHom.toAdditive.toIntLinearMap.intertwiningMap_of_isIntertwiningMap
    (Rep.res r I[K₀]).ρ (I[M₀]).ρ ?_)
  intro σ a
  apply Additive.toMul.injective
  exact towerRelativeIdeleBaseChangeMulEquiv_unflatten_conjugation K₀ M₀ L₀ σ a.toMul

/-- The fixed-top local tensor coefficient map for restriction. -/
def localTensorBaseRestrictionRepHom {A B : Type} [CommRing A] [CommRing B]
    [Algebra K₀ A] [Algebra K₀ B] [Algebra M₀ B] [IsScalarTower K₀ M₀ B]
    (f : A →ₐ[K₀] B) : Rep.res r T[K₀, A] ⟶ T[M₀, B] := by
  let t := Units.map (localTensorBaseRestriction K₀ M₀ L₀ f).toRingHom.toMonoidHom
  refine Rep.ofHom (t.toAdditive.toIntLinearMap.intertwiningMap_of_isIntertwiningMap
    (Rep.res r T[K₀, A]).ρ (T[M₀, B]).ρ ?_)
  intro σ a
  apply Additive.toMul.injective
  apply Units.ext
  let a₀ : Additive (A ⊗[K₀] L₀)ˣ := a
  exact localTensorBaseRestriction_conjugation K₀ M₀ L₀ f σ a₀.toMul.val

omit [NumberField L₀] [FiniteDimensional M₀ L₀] [FiniteDimensional K₀ L₀]
    [IsGalois K₀ L₀] [IsGalois M₀ L₀] in
/-- Restricting a full idèle cohomology class and evaluating at a finite upper place
agrees with evaluating at its lower place and restricting that tensor class. -/
theorem finiteIdeleH2_finiteTensor_baseRestriction
    (W : HeightOneSpectrum (𝓞 M₀)) :
    groupCohomology.map r
        (relativeIdeleBaseRestrictionRepHom (K₀ := K₀) (M₀ := M₀) (L₀ := L₀)) 2 ≫
        groupCohomology.map (A := I[M₀]) (MonoidHom.id (Gal(L₀/M₀)))
          (finiteIdeleFiniteTensorRepHom M₀ L₀ W) 2 =
      groupCohomology.map (A := I[K₀]) (MonoidHom.id (Gal(L₀/K₀)))
        (finiteIdeleFiniteTensorRepHom K₀ L₀ (finitePlaceBelow (K := K₀) W)) 2 ≫
        groupCohomology.map r (localTensorBaseRestrictionRepHom (L₀ := L₀)
          (finiteCompletionBaseRestriction K₀ M₀ W)) 2 := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (by simp only [MonoidHom.comp_id, MonoidHom.id_comp])
  apply LinearMap.ext
  intro a
  let a₀ : Additive (RelativeIdeleGroup K₀ L₀) := a
  apply Additive.toMul.injective
  exact relativeIdeleBaseRestriction_finite K₀ M₀ L₀ W a₀.toMul

omit [NumberField L₀] [FiniteDimensional M₀ L₀] [FiniteDimensional K₀ L₀]
    [IsGalois K₀ L₀] [IsGalois M₀ L₀] in
/-- The same restriction square at every archimedean place. -/
theorem finiteIdeleH2_infiniteTensor_baseRestriction
    (W : InfinitePlace M₀) :
    let _ : IsScalarTower K₀ M₀ W.Completion := infiniteCompletionBaseTower K₀ M₀ W
    groupCohomology.map r
        (relativeIdeleBaseRestrictionRepHom (K₀ := K₀) (M₀ := M₀) (L₀ := L₀)) 2 ≫
        groupCohomology.map (A := I[M₀]) (MonoidHom.id (Gal(L₀/M₀)))
          (finiteIdeleInfiniteTensorRepHom M₀ L₀ W) 2 =
      groupCohomology.map (A := I[K₀]) (MonoidHom.id (Gal(L₀/K₀)))
        (finiteIdeleInfiniteTensorRepHom K₀ L₀ (infinitePlaceBelow (K := K₀) W)) 2 ≫
        groupCohomology.map r (localTensorBaseRestrictionRepHom (L₀ := L₀)
          (infiniteCompletionBaseRestriction K₀ M₀ W)) 2 := by
  intro hTower
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (by simp only [MonoidHom.comp_id, MonoidHom.id_comp])
  apply LinearMap.ext
  intro a
  let a₀ : Additive (RelativeIdeleGroup K₀ L₀) := a
  apply Additive.toMul.injective
  exact relativeIdeleBaseRestriction_infinite K₀ M₀ L₀ W a₀.toMul

end Cohomology

end GlobalClassFieldTheory.Cohomology
