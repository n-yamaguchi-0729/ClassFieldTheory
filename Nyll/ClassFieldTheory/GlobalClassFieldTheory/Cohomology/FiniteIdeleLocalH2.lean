/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteIdeleH2Injection
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SupportedIdeleH2Localization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandOutsideSupport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.SupportedIdelePrescribedH2

/-! # Localization detects the degree-two cohomology of the full idèle group -/

@[expose] public section

open CategoryTheory ClassFieldTower.Martinet.Shafarevich IsDedekindDomain NumberField
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped NumberField TensorProduct

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "GalGroup" => Gal(L/K)
local notation "I" => (ShortComplex.X₂ (C := Rep ℤ Gal(L/K)) (finiteIdeleShortComplex K L))
local notation "J" S => relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S
local notation "Iₛ[" T "]" =>
  (ShortComplex.X₂ (C := Rep ℤ Gal(L/K)) (supportedIdeleClassShortComplex K L T))
local notation "S₀" => ideleClassHerbrandSupport (K := K) (L := L)

local instance : MulDistribMulAction GalGroup (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L

local instance (S : Finset (HeightOneSpectrum (𝓞 K))) : MulDistribMulAction GalGroup (J S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction GalGroup (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

local instance (v : InfinitePlace K) : MulDistribMulAction GalGroup (v.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.Completion)

/-- Include actual supported idèle coefficients into the full idèle representation. -/
def supportedIdeleInclusionRepHom (S : Finset (HeightOneSpectrum (𝓞 K))) : Iₛ[S] ⟶ I :=
  equivariantRepHom (G := GalGroup) (A := J S) (B := RelativeIdeleGroup K L) (J S).subtype
    (fun _ _ => rfl)

/-- Project a full relative idèle coefficient to its actual finite tensor coordinate. -/
def finiteIdeleFiniteTensorRepHom (v : HeightOneSpectrum (𝓞 K)) :
    I ⟶ Rep.ofMulDistribMulAction GalGroup (v.adicCompletion K ⊗[K] L)ˣ :=
  equivariantRepHom (RelativeIdeleGroup.finiteComponent (K := K) (L := L) v)
    (RelativeIdeleGroup.finiteComponent_smul (K := K) (L := L) v)

/-- Project a full relative idèle coefficient to its actual archimedean tensor coordinate. -/
def finiteIdeleInfiniteTensorRepHom (v : InfinitePlace K) :
    I ⟶ Rep.ofMulDistribMulAction GalGroup (v.Completion ⊗[K] L)ˣ :=
  equivariantRepHom (RelativeIdeleGroup.infiniteComponent (K := K) (L := L) v)
    (RelativeIdeleGroup.infiniteComponent_smul (K := K) (L := L) v)

omit [IsGalois K L] in
/-- A representative two-cocycle has only finitely many coefficient values.
Their supports, enlarged by the Herbrand support, give an actual supported
degree-two preimage of any full idèle class. -/
theorem exists_supportedIdeleH2_preimage (x : groupCohomology I 2) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S ∧
      ∃ y : groupCohomology (Iₛ[S]) 2,
        groupCohomology.map (A := Iₛ[S]) (B := I) (MonoidHom.id GalGroup)
          (supportedIdeleInclusionRepHom K L S) 2 y = x := by
  classical
  let : Fintype GalGroup := Fintype.ofFinite GalGroup
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    let a (p : GalGroup × GalGroup) : Additive (RelativeIdeleGroup K L) := c p
    let support (p : GalGroup × GalGroup) :=
      relativeIdeleLocalTensorDecompositionSupport (K := K) (L := L) (a p).toMul
    let S := S₀ ∪ Finset.univ.biUnion support
    have hm (p : GalGroup × GalGroup) : (a p).toMul ∈ J S := by
      apply relativeIdeleLocalTensorDecompositionSupportedSubgroup_mono
        (K := K) (L := L) (S := support p) (T := S) ?_
        (relativeIdele_mem_localTensorDecompositionSupportedSubgroup (K := K) (L := L) _)
      intro v hv
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hv⟩)
    let d₀ (p : GalGroup × GalGroup) : Iₛ[S] := Additive.ofMul ⟨(a p).toMul, hm p⟩
    let d : groupCohomology.cocycles₂ (Iₛ[S]) := ⟨d₀, by
      apply (groupCohomology.mem_cocycles₂_iff d₀).mpr
      intro g h j
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun u : I => (show Additive (RelativeIdeleGroup K L) from u).toMul)
        ((groupCohomology.mem_cocycles₂_iff c).mp c.property g h j)⟩
    refine ⟨S, Finset.subset_union_left, groupCohomology.H2π (Iₛ[S]) d, ?_⟩
    rw [groupCohomology.H2π_comp_map_apply]
    rfl

/-- If all actual finite and archimedean tensor coordinates of a full
degree-two idèle class vanish, then the original class vanishes. -/
theorem finiteIdeleH2_eq_zero_of_localizations (x : groupCohomology I 2)
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K), groupCohomology.map (A := I) (MonoidHom.id GalGroup)
      (finiteIdeleFiniteTensorRepHom K L v) 2 x = 0)
    (hinfinite : ∀ v : InfinitePlace K, groupCohomology.map (A := I) (MonoidHom.id GalGroup)
      (finiteIdeleInfiniteTensorRepHom K L v) 2 x = 0) : x = 0 := by
  obtain ⟨S, hS, y, rfl⟩ := exists_supportedIdeleH2_preimage K L x
  have hfin (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :=
    chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := L) v (fun h => hv (hS h))
  have hy : y = 0 := by
    apply supportedSPlaceH2_eq_zero_of_localizations K L S hfin
    · intro v
      have he : supportedIdeleInclusionRepHom K L S ≫ finiteIdeleFiniteTensorRepHom K L v.val =
          supportedSPlaceFiniteRepHom K L S v := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro a
        rfl
      have h := hfinite v.val
      change (groupCohomology.map (A := Iₛ[S]) (B := I) (MonoidHom.id GalGroup)
        (supportedIdeleInclusionRepHom K L S) 2 ≫
        groupCohomology.map (A := I) (MonoidHom.id GalGroup)
          (finiteIdeleFiniteTensorRepHom K L v.val) 2) y = 0 at h
      rwa [← groupCohomology.map_id_comp, he] at h
    · intro v
      have he : supportedIdeleInclusionRepHom K L S ≫ finiteIdeleInfiniteTensorRepHom K L v =
          supportedSPlaceInfiniteRepHom K L S v := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro a
        rfl
      have h := hinfinite v
      change (groupCohomology.map (A := Iₛ[S]) (B := I) (MonoidHom.id GalGroup)
        (supportedIdeleInclusionRepHom K L S) 2 ≫
        groupCohomology.map (A := I) (MonoidHom.id GalGroup)
          (finiteIdeleInfiniteTensorRepHom K L v) 2) y = 0 at h
      rwa [← groupCohomology.map_id_comp, he] at h
  rw [hy, map_zero]

end GlobalClassFieldTheory.Cohomology
