/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorInflation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleLocalBrauerRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleH2KernelByInvariantSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassInflation

/-! # Inflation of full idèles to a common Galois refinement -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped NumberField TensorProduct

noncomputable section
namespace GlobalClassFieldTheory.Cohomology
attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E] [Algebra K M] [Algebra K E]
  [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E]
  (j : M →ₐ[K] E)

local notation "I" F => ShortComplex.X₂ (finiteIdeleShortComplex K F)
local notation "q" F =>
  ShortComplex.g (finiteIdeleShortComplex K F) ≫
    Iso.hom (relativeToStandardIdeleClassRepIso K F)
local notation "r" => ContinuousMonoidHom.toMonoidHom (embeddedGaloisRestriction (B := K) j)
local notation "A" => NumberField.AdeleRing (𝓞 K) K

/-- The actual scalar inclusion on full idèles, as an equivariant coefficient map. -/
def relativeIdeleInflationRepHom : Rep.res r (I M) ⟶ I E := by
  let f := Algebra.TensorProduct.map (AlgHom.id K A) j
  refine Rep.ofHom ⟨(Units.map f.toMonoidHom).toAdditive.toIntLinearMap, fun σ => ?_⟩
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  let u₀ : Additive (RelativeIdeleGroup K M) := u
  change f (RelativeIdeleGroup.conjugation K M (embeddedGaloisRestriction (B := K) j σ)
      (u₀.toMul : RelativeAdeleRing K M)) =
    RelativeIdeleGroup.conjugation K E σ (f (u₀.toMul : RelativeAdeleRing K M))
  generalize (u₀.toMul : RelativeAdeleRing K M) = z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [f, RelativeIdeleGroup.conjugation_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, embeddedGaloisRestriction_commutes]

/-- Inflation on full idèles uses the actual restriction of Galois automorphisms. -/
def fullIdeleH2InflateOfEmbedding : groupCohomology (I M) 2 ⟶ groupCohomology (I E) 2 :=
  groupCohomology.map r (relativeIdeleInflationRepHom j) 2

omit [NumberField M] [NumberField E] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K E] in
private theorem fullIdeleH2Inflation_finiteTensor (v : HeightOneSpectrum (𝓞 K)) :
    fullIdeleH2InflateOfEmbedding j ≫
        groupCohomology.map (MonoidHom.id _) (finiteIdeleFiniteTensorRepHom K E v) 2 =
      groupCohomology.map (MonoidHom.id _) (finiteIdeleFiniteTensorRepHom K M v) 2 ≫
        groupCohomology.map r (tensorTopFieldInflationRepHom (F := v.adicCompletion K) j) 2 := by
  rw [fullIdeleH2InflateOfEmbedding, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (by simp only [MonoidHom.id_comp, MonoidHom.comp_id])
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  let u₀ : Additive (RelativeIdeleGroup K M) := u
  change relativeAdeleFiniteComponent (K := K) (L := E) v
      (Algebra.TensorProduct.map (AlgHom.id K A) j (u₀.toMul : RelativeAdeleRing K M)) =
    Algebra.TensorProduct.map (AlgHom.id K (v.adicCompletion K)) j
      (relativeAdeleFiniteComponent (K := K) (L := M) v (u₀.toMul : RelativeAdeleRing K M))
  generalize (u₀.toMul : RelativeAdeleRing K M) = z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, relativeAdeleFiniteComponent_tmul]

omit [NumberField M] [NumberField E] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K E] in
private theorem fullIdeleH2Inflation_infiniteTensor (v : InfinitePlace K) :
    fullIdeleH2InflateOfEmbedding j ≫
        groupCohomology.map (MonoidHom.id _) (finiteIdeleInfiniteTensorRepHom K E v) 2 =
      groupCohomology.map (MonoidHom.id _) (finiteIdeleInfiniteTensorRepHom K M v) 2 ≫
        groupCohomology.map r (tensorTopFieldInflationRepHom (F := v.Completion) j) 2 := by
  rw [fullIdeleH2InflateOfEmbedding, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (by simp only [MonoidHom.id_comp, MonoidHom.comp_id])
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  let u₀ : Additive (RelativeIdeleGroup K M) := u
  change relativeAdeleInfiniteComponent (K := K) (L := E) v
      (Algebra.TensorProduct.map (AlgHom.id K A) j (u₀.toMul : RelativeAdeleRing K M)) =
    Algebra.TensorProduct.map (AlgHom.id K v.Completion) j
      (relativeAdeleInfiniteComponent (K := K) (L := M) v (u₀.toMul : RelativeAdeleRing K M))
  generalize (u₀.toMul : RelativeAdeleRing K M) = z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, relativeAdeleInfiniteComponent_tmul]

/-- The genuine local Brauer tuple of a full idèle class is unchanged in a refinement. -/
theorem fullIdeleBrauerTuple_inflateOfEmbedding (x : groupCohomology (I M) 2) :
    fullIdeleBrauerTuple K E (fullIdeleH2InflateOfEmbedding j x) = fullIdeleBrauerTuple K M x := by
  apply DFinsupp.ext
  intro w
  cases w with
  | inl v =>
    let F := v.adicCompletion K
    let i : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
    rw [fullIdeleBrauerTuple_finite_apply, fullIdeleBrauerTuple_finite_apply]
    let p := (groupCohomology.functor ℤ Gal(E/K) 2).map (finiteIdeleFiniteTensorRepHom K E v)
    let c := (groupCohomology.functor ℤ Gal(M/K) 2).map (finiteIdeleFiniteTensorRepHom K M v)
    let t := groupCohomology.map r (tensorTopFieldInflationRepHom (F := F) j) 2
    have h : p (fullIdeleH2InflateOfEmbedding j x) = t (c x) :=
      ConcreteCategory.congr_hom (fullIdeleH2Inflation_finiteTensor j v) x
    refine (congrArg (finiteTensorH2ToBrauerOfExtension E v) h).trans ?_
    simp only [finiteTensorH2ToBrauerOfExtension]
    rw [tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ i,
      tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ (i.comp j)]
    exact absoluteTensorH2Map_topFieldInflation j i _
  | inr v =>
    let F := v.Completion
    let i : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
    rw [fullIdeleBrauerTuple_infinite_apply, fullIdeleBrauerTuple_infinite_apply]
    let p := (groupCohomology.functor ℤ Gal(E/K) 2).map (finiteIdeleInfiniteTensorRepHom K E v)
    let c := (groupCohomology.functor ℤ Gal(M/K) 2).map (finiteIdeleInfiniteTensorRepHom K M v)
    let t := groupCohomology.map r (tensorTopFieldInflationRepHom (F := F) j) 2
    have h : p (fullIdeleH2InflateOfEmbedding j x) = t (c x) :=
      ConcreteCategory.congr_hom (fullIdeleH2Inflation_infiniteTensor j v) x
    refine (congrArg (infiniteTensorH2ToBrauerOfExtension E v) h).trans ?_
    simp only [infiniteTensorH2ToBrauerOfExtension]
    rw [tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ i,
      tensorH2ToCompletedBrauer_eq_absoluteTensorH2Map _ _ _ _ (i.comp j)]
    exact absoluteTensorH2Map_topFieldInflation j i _

omit [IsGalois K M] [IsGalois K E] in
private theorem ordinaryAdeleInclusion_baseChange (z : RelativeAdeleRing K M) :
    let _ : Algebra M E := j.toRingHom.toAlgebra
    NumberField.AdeleRing.fieldInclusion M E
        (relativeAdeleBaseChangeRingEquiv (K := K) (L := M) z) =
      relativeAdeleBaseChangeRingEquiv (K := K) (L := E)
        (Algebra.TensorProduct.map (AlgHom.id K A) j z) := by
  intro algebraOwner
  let : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  let : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  have h := relativeAdeleBaseChangeRingEquiv_tower K M E (z ⊗ₜ[M] (1 : E))
  change relativeAdeleBaseChangeRingEquiv
      (towerActualRelativeAdeleRingEquiv K M E (z ⊗ₜ[M] (1 : E))) =
    relativeAdeleBaseChangeRingEquiv (towerRelativeAdeleFlatten K M E (z ⊗ₜ[M] (1 : E))) at h
  rw [towerActualRelativeAdeleRingEquiv_tmul, towerRelativeAdeleFlatten_tmul, map_one,
    mul_one] at h
  exact h

omit [IsGalois K E] in
/-- The actual standard quotient commutes with scalar inflation on full idèles. -/
theorem fullIdeleClassH2Map_inflateOfEmbedding (x : groupCohomology (I M) 2) :
    fullIdeleClassH2Map K E (fullIdeleH2InflateOfEmbedding j x) =
      standardIdeleClassH2InflateOfEmbedding j (fullIdeleClassH2Map K M x) := by
  have h : fullIdeleH2InflateOfEmbedding j ≫ groupCohomology.map (MonoidHom.id _) (q E) 2 =
      groupCohomology.map (MonoidHom.id _) (q M) 2 ≫
        standardIdeleClassH2InflateOfEmbedding j := by
    rw [fullIdeleH2InflateOfEmbedding, standardIdeleClassH2InflateOfEmbedding,
      ← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr (by simp only [MonoidHom.id_comp, MonoidHom.comp_id])
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    let u₀ : Additive (RelativeIdeleGroup K M) := u
    let : Algebra M E := j.toRingHom.toAlgebra
    let f := Algebra.TensorProduct.map (AlgHom.id K A) j
    change NumberField.IdeleClassGroup.relativeClassComparison K E
        (QuotientGroup.mk' _ (Units.map f.toMonoidHom u₀.toMul)) =
      NumberField.IdeleClassGroup.fieldInclusion M E
        (NumberField.IdeleClassGroup.relativeClassComparison K M (QuotientGroup.mk' _ u₀.toMul))
    simp only [NumberField.IdeleClassGroup.relativeClassComparison,
      relativeIdeleClassBaseChangeMulEquiv_mk]
    change QuotientGroup.mk' _
        (relativeIdeleBaseChangeMulEquiv (K := K) (L := E) (Units.map f.toMonoidHom u₀.toMul)) =
      NumberField.IdeleClassGroup.fieldInclusion M E
        (QuotientGroup.mk' _ (relativeIdeleBaseChangeMulEquiv (K := K) (L := M) u₀.toMul))
    rw [NumberField.IdeleClassGroup.fieldInclusion_mk, relativeIdeleBaseChangeMulEquiv_eq_ringUnits,
      relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
    apply congrArg (QuotientGroup.mk' _)
    apply Units.ext
    exact (ordinaryAdeleInclusion_baseChange j (u₀.toMul : RelativeAdeleRing K M)).symm
  exact ConcreteCategory.congr_hom h x

end GlobalClassFieldTheory.Cohomology
