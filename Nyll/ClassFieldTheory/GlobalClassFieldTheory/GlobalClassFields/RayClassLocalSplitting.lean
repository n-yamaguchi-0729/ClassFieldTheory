/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core

/-!
# Complete splitting through the full local ray image

At any finite place, including a place in the modulus support, the full
local multiplicative group maps into the ray class group. Its Artin image
is the actual decomposition group. Killing these full local images gives
the largest subfield of the ray class field in which the specified places
split completely.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open Reciprocity

variable {K : Type*} [Field K] [NumberField K]

/-- The entire local multiplicative group, inserted in the full ray class
group. No assumption excludes the modulus support. -/
noncomputable def finitePlaceRayClassMap (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* RayClass.RayClassGroup m :=
  (QuotientGroup.mk' m.congruenceSubgroup).comp (IdeleGroup.finitePlaceIdeleClass v)

/-- Restriction to a ray-class fixed field takes the full local ray map to
the existing local Artin map. -/
theorem rayClassSubgroupFixedFieldArtin_comp_finitePlaceRayClassMap
    (m : RayClass.Modulus K) (H : Subgroup (RayClass.RayClassGroup m))
    (v : HeightOneSpectrum (𝓞 K)) :
    (rayClassSubgroupFixedFieldArtin m H).comp (finitePlaceRayClassMap m v) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := rayClassSubgroupFixedField m H) v := by
  apply MonoidHom.ext
  intro x
  have hrec : (rayClassFieldGaloisEquivRayClassGroup m).symm
      (QuotientGroup.mk' m.congruenceSubgroup (IdeleGroup.finitePlaceIdeleClass v x)) =
      globalNormResidueMonoidHom K (rayClassField K m)
        (IdeleGroup.finitePlaceIdeleClass v x) := by
    apply (rayClassFieldGaloisEquivRayClassGroup m).symm_apply_eq.mpr
    exact (rayClassFieldGaloisEquivRayClassGroup_globalNormResidue m
      (IdeleGroup.finitePlaceIdeleClass v x)).symm
  change AlgEquiv.restrictNormalHom (rayClassSubgroupFixedField m H)
      ((rayClassFieldGaloisEquivRayClassGroup m).symm
        (QuotientGroup.mk' m.congruenceSubgroup (IdeleGroup.finitePlaceIdeleClass v x))) = _
  rw [hrec]
  have hlocal := DFunLike.congr_fun
    (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      (K := K) (L := rayClassField K m) v) x
  change globalNormResidueMonoidHom K (rayClassField K m)
    (IdeleGroup.finitePlaceIdeleClass v x) =
      chosenFinitePlaceArtinMonoidHom (K := K) (L := rayClassField K m) v x at hlocal
  rw [hlocal]
  exact DFunLike.congr_fun
    (chosenFinitePlaceArtinMonoidHom_restrict_tower
      (K := K) (L := rayClassField K m) (E := rayClassSubgroupFixedField m H) v) x

/-- The full local ray image maps onto the actual decomposition group in
the chosen fixed field, also at primes dividing the modulus. -/
theorem finitePlaceRayClassMap_range_map_artin
    (m : RayClass.Modulus K) (H : Subgroup (RayClass.RayClassGroup m))
    (v : HeightOneSpectrum (𝓞 K)) :
    (finitePlaceRayClassMap m v).range.map (rayClassSubgroupFixedFieldArtin m H) =
      finitePlaceDecompositionGroup (K := K) (L := rayClassSubgroupFixedField m H) v := by
  rw [← MonoidHom.range_comp,
    rayClassSubgroupFixedFieldArtin_comp_finitePlaceRayClassMap,
    chosenFinitePlaceArtinMonoidHom_range]

/-- Complete splitting at an arbitrary finite place is equivalent to
killing its full local image in the ray class quotient by `H`. -/
theorem finitePlaceSplitsCompletely_rayClassFixedField_iff
    (m : RayClass.Modulus K) (H : Subgroup (RayClass.RayClassGroup m))
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely (K := K) (L := rayClassSubgroupFixedField m H) v ↔
      (finitePlaceRayClassMap m v).range ≤ H := by
  change finitePlaceDecompositionGroup
    (K := K) (L := rayClassSubgroupFixedField m H) v = ⊥ ↔ _
  rw [← finitePlaceRayClassMap_range_map_artin]
  constructor
  · intro h x hx
    have hmem : rayClassSubgroupFixedFieldArtin m H x ∈
        (⊥ : Subgroup (rayClassSubgroupFixedField m H ≃ₐ[K]
          rayClassSubgroupFixedField m H)) := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    have hker : x ∈ (rayClassSubgroupFixedFieldArtin m H).ker :=
      Subgroup.mem_bot.mp hmem
    rwa [rayClassSubgroupFixedFieldArtin_ker] at hker
  · intro h
    apply le_antisymm _ bot_le
    rintro _ ⟨x, hx, rfl⟩
    apply Subgroup.mem_bot.mpr
    have hker : x ∈ (rayClassSubgroupFixedFieldArtin m H).ker := by
      rw [rayClassSubgroupFixedFieldArtin_ker]
      exact h hx
    exact hker

/-- The subgroup generated by the full local images at the specified
places, with no restriction on their intersection with the modulus support. -/
noncomputable def rayClassLocalSplittingSubgroup (m : RayClass.Modulus K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (RayClass.RayClassGroup m) :=
  ⨆ v : S, (finitePlaceRayClassMap m v.1).range

/-- The specified places split exactly in the fixed fields whose defining
subgroups contain all the corresponding local images. -/
theorem splitsCompletely_on_set_iff_rayClassLocalSplittingSubgroup_le
    (m : RayClass.Modulus K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (H : Subgroup (RayClass.RayClassGroup m)) :
    (∀ v ∈ S, FinitePlaceSplitsCompletely
      (K := K) (L := rayClassSubgroupFixedField m H) v) ↔
      rayClassLocalSplittingSubgroup m S ≤ H := by
  constructor
  · intro h
    apply iSup_le
    intro v
    exact (finitePlaceSplitsCompletely_rayClassFixedField_iff m H v.1).mp (h v.1 v.2)
  · intro h v hv
    apply (finitePlaceSplitsCompletely_rayClassFixedField_iff m H v).mpr
    exact (le_iSup (fun w : S => (finitePlaceRayClassMap m w.1).range) ⟨v, hv⟩).trans h

/-- Every specified place splits in the field constructed from its full
local images, including the places in the modulus support. -/
theorem rayClassLocalSplittingSubgroup_splitsCompletely
    (m : RayClass.Modulus K) (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∀ v ∈ S, FinitePlaceSplitsCompletely
      (K := K) (L := rayClassSubgroupFixedField m (rayClassLocalSplittingSubgroup m S)) v :=
  (splitsCompletely_on_set_iff_rayClassLocalSplittingSubgroup_le
    m S (rayClassLocalSplittingSubgroup m S)).mpr le_rfl

/-- The fixed field of the generated full local images is the largest
ray-class subfield in which all specified places split completely. -/
theorem rayClassLocalSplittingSubgroup_maximal
    (m : RayClass.Modulus K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (H : Subgroup (RayClass.RayClassGroup m))
    (h : ∀ v ∈ S, FinitePlaceSplitsCompletely
      (K := K) (L := rayClassSubgroupFixedField m H) v) :
    rayClassSubgroupFixedField m H ≤
      rayClassSubgroupFixedField m (rayClassLocalSplittingSubgroup m S) :=
  IntermediateField.fixedField_le (Subgroup.map_mono
    ((splitsCompletely_on_set_iff_rayClassLocalSplittingSubgroup_le m S H).mp h))

end GlobalClassFieldTheory.GlobalClassFields
